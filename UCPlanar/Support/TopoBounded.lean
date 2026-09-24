/- The closed region a drawn cycle bounds is a bounded set, so it holds finitely many vertices. -/
import UCPlanar.Support.TopoJordan

open Set

open scoped Classical

namespace UCPlanar.Support

/-- The closed region a drawn closed walk bounds is its trace together with what it encloses. -/
theorem closedCycleDomain_eq_union {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {o : V} (γ : G.Walk o o) :
    E.closedCycleDomain γ = E.walkTrace γ ∪ insideOf (E.walkTrace γ) := by
  ext t
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr h

/-- **The closed region a drawn cycle bounds is bounded.**  Its transported form is the Jordan
curve together with its inside. -/
theorem isBounded_closedCycleDomain {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {o : V} (γ : G.Walk o o) (hγ : γ.IsCycle) :
    Bornology.IsBounded (E.closedCycleDomain γ) := by
  rw [← isBounded_image_homeo planeHomeo]
  have hsplit : planeHomeo '' E.closedCycleDomain γ =
      topoTrace E γ ∪ Schoenflies.inside (topoTrace E γ) := by
    rw [closedCycleDomain_eq_union, Set.image_union, image_insideOf, ← insideOf_eq_inside]
    rfl
  rw [hsplit]
  exact (isCompact_topoTrace E γ).isBounded.union
    (isBounded_inside_of_isSeparating (isSeparating_topoTrace_cycle E γ hγ))

/-- **A drawn cycle of a periodic plane graph encloses finitely many vertices.**  The closed
region it bounds sits inside a square, which holds finitely many vertices. -/
theorem finite_cycleRegion {V : Type*} (Q : UCPlanar.PeriodicPlaneGraph V) {o : V}
    (γ : Q.graph.Walk o o) (hγ : γ.IsCycle) : (Q.embedding.cycleRegion γ).Finite := by
  obtain ⟨R, hR⟩ := (isBounded_closedCycleDomain Q.embedding γ hγ).subset_closedBall 0
  refine Set.Finite.subset (Q.finite_squares R) ?_
  intro x hx i
  have h1 : Q.embedding.pos x ∈ Q.embedding.closedCycleDomain γ :=
    (Q.embedding.pos_mem_closedCycleDomain_iff γ x).mpr hx
  have h2 : ‖Q.embedding.pos x‖ ≤ R := by
    have := hR h1
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this
  have h3 : ‖Q.embedding.pos x i‖ ≤ ‖Q.embedding.pos x‖ := norm_le_pi_norm _ i
  rw [Real.norm_eq_abs] at h3
  rw [← Q.embedding_pos]
  linarith

end UCPlanar.Support
