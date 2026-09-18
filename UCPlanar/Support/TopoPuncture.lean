/- A punctured ball of the plane is connected, so a point of the frontier of an open set which
the complement of the closure also reaches is not isolated in that frontier. -/
import UCPlanar.Support.TopoArcLocal
import Mathlib

open Set
open scoped Classical

namespace UCPlanar.Support

/-- **A punctured ball of the plane is preconnected.**  It is the image of the punctured plane
under the radial map `x ↦ p + (ρ / (1 + ‖x‖)) • x`, which is continuous and lands exactly on the
points at distance strictly between `0` and `ρ` from `p`. -/
theorem isPreconnected_ball_diff_singleton (p : UCPlanar.Plane) (ρ : ℝ) :
    IsPreconnected (Metric.ball p ρ \ {p}) := by
  by_cases hρ : 0 < ρ
  case neg =>
    rw [Metric.ball_eq_empty.mpr (not_lt.mp hρ)]
    simpa using isPreconnected_empty
  have himg : Metric.ball p ρ \ {p}
        = (fun x : UCPlanar.Plane => p + (ρ / (1 + ‖x‖)) • x) '' ({0}ᶜ) := by
      ext y
      constructor
      · rintro ⟨hy1, hy2⟩
        rw [Set.mem_singleton_iff] at hy2
        set s : ℝ := ‖y - p‖ with hs
        have hs0 : 0 < s := by
          rw [hs, norm_pos_iff, sub_ne_zero]
          exact hy2
        have hsρ : s < ρ := by
          rw [hs, ← dist_eq_norm]
          exact Metric.mem_ball.mp hy1
        have hden : 0 < ρ - s := by linarith
        refine ⟨(ρ - s)⁻¹ • (y - p), ?_, ?_⟩
        · intro hc
          rw [Set.mem_singleton_iff, smul_eq_zero] at hc
          rcases hc with h | h
          · exact (inv_ne_zero (ne_of_gt hden)) h
          · exact hy2 (by rwa [sub_eq_zero] at h)
        · have hnx : ‖(ρ - s)⁻¹ • (y - p)‖ = (ρ - s)⁻¹ * s := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hden), ← hs]
          simp only [hnx]
          have h1 : 1 + (ρ - s)⁻¹ * s = ρ / (ρ - s) := by
            field_simp
            ring
          rw [h1]
          have h2 : ρ / (ρ / (ρ - s)) = ρ - s := by
            field_simp
          rw [h2, smul_smul, mul_inv_cancel₀ (ne_of_gt hden), one_smul]
          abel
      · rintro ⟨x, hx, rfl⟩
        rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
        have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
        have hd : 0 < 1 + ‖x‖ := by linarith
        have hn : ‖(ρ / (1 + ‖x‖)) • x‖ = ρ * ‖x‖ / (1 + ‖x‖) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hρ hd)]
          ring
        constructor
        · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hn, div_lt_iff₀ hd]
          nlinarith
        · rw [Set.mem_singleton_iff]
          intro hc
          have hz : (ρ / (1 + ‖x‖)) • x = 0 := by
            have := congrArg (fun z => z - p) hc
            simpa using this
          rw [smul_eq_zero] at hz
          rcases hz with h | h
          · exact (ne_of_gt (div_pos hρ hd)) h
          · exact hx h
  rw [himg]
  refine (isPreconnected_compl_singleton (0 : UCPlanar.Plane)).image _
    (Continuous.continuousOn ?_)
  have hc : Continuous (fun x : UCPlanar.Plane => ρ / (1 + ‖x‖)) :=
    continuous_const.div (by fun_prop) (fun x => by positivity)
  exact continuous_const.add (hc.smul continuous_id')

/-- **A point of the frontier of an open set that the complement of its closure also reaches is
not isolated in that frontier.**  Otherwise a punctured ball around it would be split by the two
disjoint open sets `U` and the complement of `closure U`, both of which it meets. -/
theorem exists_mem_frontier_ne (U : Set UCPlanar.Plane) (hU : IsOpen U) {p : UCPlanar.Plane}
    (hin : p ∈ closure U) (hout : p ∈ closure (closure U)ᶜ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q ∈ frontier U, q ∈ Metric.ball p ε ∧ q ≠ p := by
  by_contra hcon
  push Not at hcon
  have hpU : p ∉ U := by
    intro hc
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp hout U hU hc
    exact hz2 (subset_closure hz1)
  have hfr : frontier U = closure U \ U := hU.frontier_eq
  have hcov : Metric.ball p ε \ {p} ⊆ U ∪ (closure U)ᶜ := by
    rintro q ⟨hq1, hq2⟩
    rw [Set.mem_singleton_iff] at hq2
    by_cases hqU : q ∈ U
    · exact Or.inl hqU
    · by_cases hqc : q ∈ closure U
      · exact absurd (hcon q (by rw [hfr]; exact ⟨hqc, hqU⟩) hq1) (by simpa using hq2)
      · exact Or.inr hqc
  have h1 : ((Metric.ball p ε \ {p}) ∩ U).Nonempty := by
    obtain ⟨y, hy1, hy2⟩ :=
      mem_closure_iff.mp hin (Metric.ball p ε) Metric.isOpen_ball (Metric.mem_ball_self hε)
    exact ⟨y, ⟨hy1, by simp only [Set.mem_singleton_iff]; rintro rfl; exact hpU hy2⟩, hy2⟩
  have h2 : ((Metric.ball p ε \ {p}) ∩ (closure U)ᶜ).Nonempty := by
    obtain ⟨y, hy1, hy2⟩ :=
      mem_closure_iff.mp hout (Metric.ball p ε) Metric.isOpen_ball (Metric.mem_ball_self hε)
    exact ⟨y, ⟨hy1, by simp only [Set.mem_singleton_iff]; rintro rfl; exact hy2 hin⟩, hy2⟩
  obtain ⟨q, -, hqU, hqc⟩ :=
    isPreconnected_ball_diff_singleton p ε U (closure U)ᶜ hU isClosed_closure.isOpen_compl
      hcov h1 h2
  exact hqc (subset_closure hqU)

end UCPlanar.Support
