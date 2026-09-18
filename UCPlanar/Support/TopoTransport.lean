/- Transport of arcs, Jordan curves and Jordan domains along a homeomorphism. -/
import UCPlanar.Support.TopoCrosscut
import Schoenflies.JordanSchoenflies

open Set unitInterval

namespace UCPlanar.Support

/-- A homeomorphism between proper metric spaces preserves boundedness in both directions. -/
theorem isBounded_image_homeo {X Y : Type*} [MetricSpace X] [ProperSpace X]
    [MetricSpace Y] [ProperSpace Y] (Φ : X ≃ₜ Y) (S : Set X) :
    Bornology.IsBounded (Φ '' S) ↔ Bornology.IsBounded S := by
  constructor
  · intro h
    have h2 : IsCompact (Φ.symm '' closure (Φ '' S)) := h.isCompact_closure.image Φ.symm.continuous
    have h4 : Φ.symm '' (Φ '' S) = S := by rw [← Set.image_comp]; simp
    have h5 : IsCompact (closure S) := by
      rw [← h4, ← Φ.symm.image_closure]; exact h2
    exact h5.isBounded.subset subset_closure
  · intro h
    have h2 : IsCompact (Φ '' closure S) := h.isCompact_closure.image Φ.continuous
    have h5 : IsCompact (closure (Φ '' S)) := by rw [← Φ.image_closure]; exact h2
    exact h5.isBounded.subset subset_closure

/-- The bounded complementary components of a set, in any ambient space. -/
def insideOf {X : Type*} [TopologicalSpace X] [Bornology X] (S : Set X) : Set X :=
  {x | x ∉ S ∧ Bornology.IsBounded (connectedComponentIn Sᶜ x)}

theorem insideOf_eq_inside (S : Set Schoenflies.Plane) :
    insideOf S = Schoenflies.inside S := rfl

/-- The Jordan domain of a set transports along a homeomorphism of proper metric spaces. -/
theorem image_insideOf {X Y : Type*} [MetricSpace X] [ProperSpace X]
    [MetricSpace Y] [ProperSpace Y] (Φ : X ≃ₜ Y) (S : Set X) :
    Φ '' insideOf S = insideOf (Φ '' S) := by
  have hcompl : Φ '' Sᶜ = (Φ '' S)ᶜ := Φ.toEquiv.image_compl S
  ext z
  constructor
  · rintro ⟨x, ⟨hxS, hxb⟩, rfl⟩
    refine ⟨fun hmem => ?_, ?_⟩
    · obtain ⟨y, hy, hxy⟩ := hmem
      exact hxS (Φ.injective hxy ▸ hy)
    · have hc := Φ.image_connectedComponentIn (s := Sᶜ) hxS
      rw [hcompl] at hc
      rw [← hc]
      exact (isBounded_image_homeo Φ _).mpr hxb
  · rintro ⟨hzS, hzb⟩
    have hmem : Φ.symm z ∈ Sᶜ := fun hmem => hzS ⟨Φ.symm z, hmem, by simp⟩
    have hz : Φ (Φ.symm z) = z := by simp
    refine ⟨Φ.symm z, ⟨hmem, ?_⟩, hz⟩
    have hc := Φ.image_connectedComponentIn (s := Sᶜ) hmem
    rw [hcompl, hz] at hc
    rw [← isBounded_image_homeo Φ, hc]
    exact hzb

/-- The Jordan domain of a plane set transports along a plane homeomorphism. -/
theorem image_inside (Φ : Schoenflies.Plane ≃ₜ Schoenflies.Plane) (S : Set Schoenflies.Plane) :
    Φ '' Schoenflies.inside S = Schoenflies.inside (Φ '' S) :=
  image_insideOf Φ S

/-- An arc transports along a homeomorphism. -/
theorem isArcBetween_image {X : Type*} [TopologicalSpace X]
    (Φ : X ≃ₜ Schoenflies.Plane) {A : Set X} {p q : X}
    (f : ℝ → X) (hc : ContinuousOn f I) (hi : InjOn f I) (him : f '' I = A)
    (h0 : f 0 = p) (h1 : f 1 = q) :
    Schoenflies.IsArcBetween (Φ '' A) (Φ p) (Φ q) := by
  refine ⟨fun t => Φ (f t), Φ.continuous.comp_continuousOn hc, Φ.injective.comp_injOn hi, ?_,
    by simp only []; rw [h0], by simp only []; rw [h1]⟩
  rw [show (fun t => Φ (f t)) = (Φ : X → Schoenflies.Plane) ∘ f from rfl, Set.image_comp, him]

/-- An arc of the plane transports along a plane homeomorphism. -/
theorem isArcBetween_image_plane (Φ : Schoenflies.Plane ≃ₜ Schoenflies.Plane)
    {A : Set Schoenflies.Plane} {p q : Schoenflies.Plane} (h : Schoenflies.IsArcBetween A p q) :
    Schoenflies.IsArcBetween (Φ '' A) (Φ p) (Φ q) := by
  obtain ⟨f, hc, hi, him, h0, h1⟩ := h
  exact isArcBetween_image Φ f hc hi him h0 h1

/-- A Jordan curve transports along a plane homeomorphism. -/
theorem isJordanCurve_image (Φ : Schoenflies.Plane ≃ₜ Schoenflies.Plane)
    {C : Set Schoenflies.Plane} (h : Schoenflies.IsJordanCurve C) :
    Schoenflies.IsJordanCurve (Φ '' C) := by
  obtain ⟨f, hf, him⟩ := h
  refine ⟨fun t => Φ (f t), ⟨Φ.continuous.comp_continuousOn hf.continuousOn, ?_, ?_⟩, ?_⟩
  · exact congrArg Φ hf.closes
  · exact Φ.injective.comp_injOn hf.injOn
  · rw [show (fun t => Φ (f t)) = (Φ : Schoenflies.Plane → Schoenflies.Plane) ∘ f from rfl,
      Set.image_comp, him]

/-- A cut pair transports along a plane homeomorphism. -/
theorem isCutPair_image (Φ : Schoenflies.Plane ≃ₜ Schoenflies.Plane)
    {C A₁ A₂ : Set Schoenflies.Plane} {p q : Schoenflies.Plane}
    (h : Schoenflies.IsCutPair C p q A₁ A₂) :
    Schoenflies.IsCutPair (Φ '' C) (Φ p) (Φ q) (Φ '' A₁) (Φ '' A₂) where
  fst := isArcBetween_image_plane Φ h.fst
  snd := isArcBetween_image_plane Φ h.snd
  union_eq := by rw [← Set.image_union, h.union_eq]
  inter_eq := by
    rw [← Set.image_inter Φ.injective, h.inter_eq, Set.image_insert_eq, Set.image_singleton]

end UCPlanar.Support
