/- A plane homeomorphism carrying one arc of a Jordan curve onto a polygonal arc. -/
import UCPlanar.Support.TopoTransport

open Set unitInterval

namespace UCPlanar.Support

/-- The lower half of the parameter interval traverses the first arc. -/
theorem image_concatenate_lowerHalf (f g : ℝ → Schoenflies.Plane) :
    Schoenflies.concatenate f g '' Schoenflies.lowerHalf = f '' I := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨2 * t, Schoenflies.double_mem_I ht, (Schoenflies.concatenate_of_le ht.2).symm⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u / 2, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
    rw [Schoenflies.concatenate_of_le (by linarith [hu.2])]
    congr 1
    ring

/-- The upper half of the parameter interval traverses the second arc. -/
theorem image_concatenate_upperHalf {f g : ℝ → Schoenflies.Plane} (hmid : f 1 = g 0) :
    Schoenflies.concatenate f g '' Schoenflies.upperHalf = g '' I := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨2 * t - 1, Schoenflies.doubleBack_mem_I ht,
      (Schoenflies.concatenate_upperHalf hmid ht).symm⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨(u + 1) / 2, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
    rw [Schoenflies.concatenate_upperHalf hmid ⟨by linarith [hu.1], by linarith [hu.2]⟩]
    congr 1
    ring

/-- Two arcs sharing both of their ends are the two halves of one loop. -/
theorem exists_loop_halves {A B : Set Schoenflies.Plane} {a b : Schoenflies.Plane}
    (hA : Schoenflies.IsArcBetween A a b) (hB : Schoenflies.IsArcBetween B b a)
    (hmeet : ∀ z ∈ A, z ∈ B → z = a ∨ z = b) :
    ∃ F : ℝ → Schoenflies.Plane, Schoenflies.IsLoop F ∧ F '' I = A ∪ B ∧
      F '' Schoenflies.lowerHalf = A ∧ F '' Schoenflies.upperHalf = B := by
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := hA
  obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := hB
  have hmid : f 1 = g 0 := by rw [hf1, hg0]
  have hclose : g 1 = f 0 := by rw [hg1, hf0]
  have hmeet' : ∀ z ∈ f '' I, z ∈ g '' I → z = f 0 ∨ z = f 1 := by
    intro z hz hz'
    rw [hfim] at hz
    rw [hgim] at hz'
    rw [hf0, hf1]
    exact hmeet z hz hz'
  refine ⟨Schoenflies.concatenate f g,
    Schoenflies.IsLoop.concatenate hfc hfi hgc hgi hmid hclose hmeet', ?_, ?_, ?_⟩
  · rw [Schoenflies.image_concatenate hmid, hfim, hgim]
  · rw [image_concatenate_lowerHalf, hfim]
  · rw [image_concatenate_upperHalf hmid, hgim]

/-- The two sides from the corner `(1,1)` to the corner `(-1,-1)` are a polygonal arc. -/
theorem isPolygonal_upperSides :
    Schoenflies.IsPolygonal (Schoenflies.sideTop ∪ Schoenflies.sideLeft) := by
  refine ⟨[Schoenflies.cornerNE, Schoenflies.cornerNW, Schoenflies.cornerSW], ?_⟩
  rw [Schoenflies.poly_cons_cons, Schoenflies.poly_pair]
  rfl

/-- **Every arc of a Jordan curve is polygonal after a homeomorphism of the plane.** Two arcs
sharing both ends are carried onto the two halves of the boundary of the model square, so the
first becomes a union of two segments. -/
theorem exists_polygonalizing_homeomorph {A B : Set Schoenflies.Plane} {a b : Schoenflies.Plane}
    (hA : Schoenflies.IsArcBetween A a b) (hB : Schoenflies.IsArcBetween B b a)
    (hmeet : ∀ z ∈ A, z ∈ B → z = a ∨ z = b) :
    ∃ Φ : Schoenflies.Plane ≃ₜ Schoenflies.Plane,
      Φ '' A = Schoenflies.sideTop ∪ Schoenflies.sideLeft ∧
      Φ '' B = Schoenflies.sideBottom ∪ Schoenflies.sideRight := by
  obtain ⟨F, hF, hFI, hFlow, hFup⟩ := exists_loop_halves hA hB hmeet
  obtain ⟨G, hG, hGI, hGlow, hGup⟩ := exists_loop_halves
    Schoenflies.isArcBetween_upperSides Schoenflies.isArcBetween_lowerSides
    Schoenflies.upperSides_meet_lowerSides
  obtain ⟨e, he⟩ := hF.exists_homeomorph hG
  have hJF : Schoenflies.IsJordanCurve (F '' I) := by
    rw [hFI]; exact Schoenflies.IsJordanCurve.of_two_arcs hA hB hmeet
  have hJG : Schoenflies.IsJordanCurve (G '' I) := by
    rw [hGI]
    exact Schoenflies.IsJordanCurve.of_two_arcs Schoenflies.isArcBetween_upperSides
      Schoenflies.isArcBetween_lowerSides Schoenflies.upperSides_meet_lowerSides
  obtain ⟨Φ, hΦ⟩ := Schoenflies.jordan_schoenflies_of_homeomorph hJF hJG e
  have hkey : ∀ t ∈ I, Φ (F t) = G t := by
    intro t ht
    rw [hΦ ⟨F t, mem_image_of_mem F ht⟩]
    exact he t ht
  have himg : ∀ S ⊆ I, Φ '' (F '' S) = G '' S := by
    intro S hS
    ext z
    constructor
    · rintro ⟨w, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t, ht, (hkey t (hS ht)).symm⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨F t, mem_image_of_mem F ht, hkey t (hS ht)⟩
  refine ⟨Φ, ?_, ?_⟩
  · rw [← hFlow, himg _ Schoenflies.lowerHalf_subset_I, hGlow]
  · rw [← hFup, himg _ Schoenflies.upperHalf_subset_I, hGup]

end UCPlanar.Support
