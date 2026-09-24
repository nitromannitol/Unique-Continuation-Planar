/- Alternating crosscuts intersect, for a crosscut that is only a topological arc. -/
import UCPlanar.Support.TopoModel

open Set unitInterval

namespace UCPlanar.Support

/-- **Alternating crosscuts of a Jordan curve meet, with no polygonality assumed.** The first
crosscut is an arbitrary arc of the Jordan domain; a homeomorphism of the plane carries it onto
two sides of a square, where the polygonal crosscut theorem applies. -/
theorem alternating_inter_nonempty_arc {C A₁ A₂ P Q : Set Schoenflies.Plane}
    {p q w₁ w₂ : Schoenflies.Plane}
    (hC : Schoenflies.IsJordanCurve C)
    (hP : Schoenflies.IsArcBetween P p q)
    (hPC : P \ {p, q} ⊆ Schoenflies.inside C)
    (hp : p ∈ C) (hq : q ∈ C)
    (hcut : Schoenflies.IsCutPair C p q A₁ A₂)
    (hQ : IsPreconnected Q) (hQside : Q ⊆ Schoenflies.inside C)
    (hw₁ : w₁ ∈ closure Q) (hw₂ : w₂ ∈ closure Q)
    (hw₁A : w₁ ∈ A₁) (hw₁B : w₁ ∉ A₂) (hw₂B : w₂ ∈ A₂) (hw₂A : w₂ ∉ A₁) :
    (Q ∩ P).Nonempty := by
  classical
  -- The first crosscut meets the curve only at its two ends.
  have hPmeet : ∀ z ∈ P, z ∈ A₁ → z = p ∨ z = q := by
    intro z hz hzA
    by_contra hne
    push Not at hne
    have hzin : z ∈ Schoenflies.inside C := hPC ⟨hz, by simp [hne.1, hne.2]⟩
    exact hzin.1 (hcut.fst_subset hzA)
  obtain ⟨Φ, hΦP, hΦA⟩ := exists_polygonalizing_homeomorph hP hcut.fst.reverse hPmeet
  -- Transport the whole configuration.
  have hCimg : Schoenflies.IsJordanCurve (Φ '' C) := isJordanCurve_image Φ hC
  have hcut' : Schoenflies.IsCutPair (Φ '' C) (Φ p) (Φ q) (Φ '' A₁) (Φ '' A₂) :=
    isCutPair_image Φ hcut
  have hdiff : Φ '' P \ {Φ p, Φ q} = Φ '' (P \ {p, q}) := by
    rw [Set.image_sdiff Φ.injective, Set.image_insert_eq, Set.image_singleton]
  have hcross : Schoenflies.IsCrosscut (Φ '' C) (Φ '' P) (Φ p) (Φ q) := by
    refine ⟨hCimg, isArcBetween_image_plane Φ hP, ?_, Set.mem_image_of_mem _ hp,
      Set.mem_image_of_mem _ hq, ?_⟩
    · rw [hΦP]
      exact isPolygonal_upperSides
    · rw [hdiff, ← image_inside Φ C]
      exact Set.image_mono hPC
  have hQ' : IsPreconnected (Φ '' Q) := hQ.image _ Φ.continuous.continuousOn
  have hQside' : Φ '' Q ⊆ Schoenflies.inside (Φ '' C) := by
    rw [← image_inside Φ C]; exact Set.image_mono hQside
  have hcl : ∀ w ∈ closure Q, Φ w ∈ closure (Φ '' Q) := by
    intro w hw
    rw [← Φ.image_closure]
    exact Set.mem_image_of_mem _ hw
  have hnot : ∀ (S : Set Schoenflies.Plane) (w : Schoenflies.Plane), w ∉ S → Φ w ∉ Φ '' S := by
    rintro S w hw ⟨y, hy, hxy⟩
    exact hw (Φ.injective hxy ▸ hy)
  obtain ⟨z, hzQ, hzP⟩ := alternating_inter_nonempty_general hcross hcut' hQ' hQside'
    (hcl _ hw₁) (hcl _ hw₂) (Set.mem_image_of_mem _ hw₁A) (hnot _ _ hw₁B)
    (Set.mem_image_of_mem _ hw₂B) (hnot _ _ hw₂A)
  obtain ⟨x, hxQ, rfl⟩ := hzQ
  obtain ⟨y, hyP, hxy⟩ := hzP
  exact ⟨x, hxQ, Φ.injective hxy ▸ hyP⟩

end UCPlanar.Support
