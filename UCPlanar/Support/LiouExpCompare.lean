/-
The exponential comparison that closes the Liouville assembly.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt

open scoped Classical

namespace UCPlanar.Support

/-- If the linear rate of the upper bound is strictly below the exponential rate of the
lower bound, then for all large scales the upper bound is below the lower bound. -/
theorem exp_upper_lt_exp_lower {A b ε C : ℝ} (_hA : 0 < A) (_hb : 0 < b) (_hε : 0 ≤ ε)
    (_hC : 0 < C) (h : A * Real.sqrt ε * C < b) :
    ∃ N : ℕ, Real.exp (A * Real.sqrt ε * C * (N + 1)) < Real.exp (b * N) := by
  set s : ℝ := A * Real.sqrt ε * C with hs
  have hs_lt : s < b := h
  have hbs : 0 < b - s := sub_pos.mpr hs_lt
  refine ⟨Nat.ceil ((s + 1) / (b - s)) + 1, ?_⟩
  apply Real.exp_lt_exp.mpr
  have hN : (s + 1) / (b - s) ≤ ((Nat.ceil ((s + 1) / (b - s)) : ℕ) : ℝ) := Nat.le_ceil _
  rw [div_le_iff₀ hbs] at hN
  push_cast
  nlinarith

end UCPlanar.Support
