/-
The dyadic ladder of the exponential lower bound.

From the scale `K₀` up to the scale `N` the chain dichotomy is applied at each of the `l`
doublings.  Either one doubling is an exponential gain, and then the logarithm of the maximum at
the top is at least `c₁` times the scale one doubling below, or every doubling multiplies that
logarithm by `32`, and then it is at least `32^l log 2`.  Both alternatives exceed `bN` for a
small enough `b`.
-/
import UCPlanar.Support.LowerArith

open scoped Classical
set_option autoImplicit false

namespace UCPlanar.Support.Lower

/-- **Theorem (B) from the chain dichotomy.**  `Mx` is the maximum of `|f|` over the square of a
given radius; the hypotheses are its monotonicity, the bootstrap `2 ≤ Mx K₀` at the bottom of the
ladder, and the chain dichotomy at each of the `l` doublings. -/
theorem theoremB_abstract (Mx : ℝ → ℝ) (c₁ b K₀ : ℝ) (N l : ℕ)
    (hK₀ : 0 < K₀) (hc₁ : 0 < c₁)
    (hmono : ∀ r s : ℝ, r ≤ s → Mx r ≤ Mx s)
    (hone : ∀ r : ℝ, K₀ ≤ r → 1 ≤ Mx r)
    (hboot : 2 ≤ Mx K₀)
    (hstep : ∀ i, i < l →
      min (32 * Real.log (Mx ((2:ℝ)^i*K₀))) (Real.log (Mx ((2:ℝ)^i*K₀)) + c₁*((2:ℝ)^i*K₀))
        ≤ Real.log (Mx ((2:ℝ)^(i+1)*K₀)))
    (htop : (2:ℝ)^l * K₀ ≤ (N:ℝ))
    (hb1 : b * (N:ℝ) ≤ Real.log 2 * 32^l)
    (hb2 : b * (N:ℝ) ≤ c₁ * ((2:ℝ)^(l-1)*K₀)) :
    Real.exp (b*(N:ℝ)) ≤ Mx (N:ℝ) := by
  set w : ℕ → ℝ := fun i => Real.log (Mx ((2:ℝ)^i*K₀)) with hw
  set Kf : ℕ → ℝ := fun i => (2:ℝ)^i*K₀ with hKf
  have hKpos : ∀ i, 0 < Kf i := fun i => by positivity
  have hKdouble : ∀ i, Kf (i+1) = 2 * Kf i := by
    intro i; simp [hKf, pow_succ]; ring
  have hKge : ∀ i, K₀ ≤ Kf i := by
    intro i
    have h1 : (1:ℝ) ≤ (2:ℝ)^i := one_le_pow₀ (by norm_num)
    simpa [hKf] using le_mul_of_one_le_left hK₀.le h1
  have hMone : ∀ i, 1 ≤ Mx (Kf i) := fun i => hone _ (hKge i)
  have hwnn : ∀ i, 0 ≤ w i := fun i => Real.log_nonneg (hMone i)
  have hkey := ladder_final l w Kf c₁ hc₁ hKpos hKdouble hwnn hstep
  have hwl : b * (N:ℝ) ≤ w l := by
    rcases hkey with h | ⟨_, h⟩
    · have h0 : Real.log 2 ≤ w 0 := by
        have : Real.log 2 ≤ Real.log (Mx ((2:ℝ)^(0:ℕ)*K₀)) := by
          refine Real.log_le_log (by norm_num) ?_
          simpa using hboot
        simpa [hw] using this
      have h1 : Real.log 2 * 32^l ≤ (32:ℝ)^l * w 0 := by
        have h2 : (0:ℝ) ≤ (32:ℝ)^l := by positivity
        nlinarith [h0, h2]
      linarith [hb1, h1, h]
    · exact le_trans hb2 h
  have hMpos : 0 < Mx (Kf l) := lt_of_lt_of_le (by norm_num) (hMone l)
  have hexp : Real.exp (b*(N:ℝ)) ≤ Mx (Kf l) := by
    have := Real.exp_le_exp.mpr hwl
    rwa [hw, Real.exp_log hMpos] at this
  exact le_trans hexp (hmono _ _ htop)

end UCPlanar.Support.Lower
