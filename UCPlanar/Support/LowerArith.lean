/-
The arithmetic of the exponential lower bound.

The three-ball inequality is used along a chain of `A` squares between the scales `K` and `2K`.
Each link of the chain is either an exponential gain or a square-root loss; a single exponential
gain already doubles the scale of the exponent, and a chain made only of square-root losses
multiplies the logarithm of the maximum by `32`.  The two branches are propagated along the
dyadic ladder of scales by the last two theorems of this module.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

open scoped Classical

namespace UCPlanar.Support.Lower

/-- One three-ball inequality splits into an exponential branch and a square-root branch. -/
theorem tb_dichotomy (C t Mi Mj : ℝ)
    (h : Mi ≤ C * Real.sqrt Mj + C * Real.exp (-t) * Mj) :
    Mi ≤ 2 * C * Real.exp (-t) * Mj ∨ Mi ≤ 2 * C * Real.sqrt Mj := by
  rcases le_total (C * Real.sqrt Mj) (C * Real.exp (-t) * Mj) with hle | hle
  · left; linarith
  · right; linarith

/-- The square-root branch in logarithmic form: once the larger maximum exceeds `(2C)^4`, the
square-root loss `Mi ≤ 2C √Mj` reads `log Mi ≤ (3/4) log Mj`. -/
theorem log_step (C Mi Mj : ℝ) (hC : 0 < C) (hMi : 0 < Mi) (hMj : 0 < Mj)
    (hbig : 4 * Real.log (2*C) ≤ Real.log Mj)
    (h : Mi ≤ 2 * C * Real.sqrt Mj) :
    Real.log Mi ≤ (3/4) * Real.log Mj := by
  have hsqrt : Real.log (Real.sqrt Mj) = Real.log Mj / 2 := Real.log_sqrt hMj.le
  have h1 : Real.log Mi ≤ Real.log (2 * C * Real.sqrt Mj) := by
    apply Real.log_le_log hMi h
  have h2 : Real.log (2 * C * Real.sqrt Mj) = Real.log (2*C) + Real.log Mj / 2 := by
    rw [Real.log_mul (by positivity) (by positivity), hsqrt]
  rw [h2] at h1
  linarith

/-- A chain of square-root losses multiplies the logarithm by `(3/4)^A`. -/
theorem log_chain (u : ℕ → ℝ) :
    ∀ n : ℕ, (∀ i, i < n → u i ≤ (3/4) * u (i+1)) → u 0 ≤ (3/4)^n * u n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hstep
    have h1 : u 0 ≤ (3/4)^n * u n := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    have h2 : u n ≤ (3/4) * u (n+1) := hstep n (Nat.lt_succ_self n)
    have h3 : (0:ℝ) ≤ (3/4)^n := by positivity
    calc u 0 ≤ (3/4)^n * u n := h1
      _ ≤ (3/4)^n * ((3/4) * u (n+1)) := by exact mul_le_mul_of_nonneg_left h2 h3
      _ = (3/4)^(n+1) * u (n+1) := by ring

/-- `(3/4)^13 < 1/32`: thirteen square-root losses beat one factor of `32`. -/
theorem three_quarters_pow_thirteen : (3/4:ℝ)^13 ≤ 1/32 := by norm_num

/-- Proposition 2.2 of the source in logarithmic form, square-root branch: a chain of `A` losses
with `(3/4)^A ≤ 1/32` multiplies the logarithm of the maximum by at least `32`. -/
theorem log_chain_pow (A : ℕ) (u : ℕ → ℝ) (hA : (3/4:ℝ)^A ≤ 1/32) (huA : 0 ≤ u A)
    (hstep : ∀ i, i < A → u i ≤ (3/4) * u (i+1)) : 32 * u 0 ≤ u A := by
  have h1 : u 0 ≤ (3/4)^A * u A := log_chain u A hstep
  have h2 : (3/4:ℝ)^A * u A ≤ (1/32) * u A := mul_le_mul_of_nonneg_right hA huA
  linarith

/-- The exponential branch propagates up the dyadic ladder: once the logarithm of the maximum at
one rung exceeds `c₁` times the previous scale, it does so at every later rung. -/
theorem ladder_exp (l : ℕ) (w K : ℕ → ℝ) (c₁ : ℝ) (hc₁ : 0 < c₁)
    (hKpos : ∀ i, 0 < K i) (hKdouble : ∀ i, K (i+1) = 2 * K i)
    (hstep : ∀ i, i < l → min (32 * w i) (w i + c₁ * K i) ≤ w (i+1)) :
    ∀ j, j < l → c₁ * K j ≤ w (j+1) → ∀ m, j < m → m ≤ l → c₁ * K (m-1) ≤ w m := by
  intro j hj hwj m hjm hml
  induction m with
  | zero => exact absurd hjm (Nat.not_lt_zero j)
  | succ m ih =>
    rcases Nat.lt_or_ge j m with hlt | hge
    · have hprev : c₁ * K (m-1) ≤ w m := ih hlt (Nat.le_of_succ_le hml)
      have hstepm : min (32 * w m) (w m + c₁ * K m) ≤ w (m+1) :=
        hstep m (Nat.lt_of_succ_le hml)
      have hm1 : 0 < m := lt_of_le_of_lt (Nat.zero_le j) hlt
      have hKm : K m = 2 * K (m-1) := by
        conv_lhs => rw [show m = (m-1)+1 from (Nat.succ_pred_eq_of_pos hm1).symm]
        exact hKdouble (m-1)
      have hA : c₁ * K m ≤ 32 * w m := by
        have : c₁ * K m = 2 * (c₁ * K (m-1)) := by rw [hKm]; ring
        nlinarith [hprev, hKpos (m-1), hc₁]
      have hB : c₁ * K m ≤ w m + c₁ * K m := by
        nlinarith [hprev, hKpos (m-1), hc₁]
      have : c₁ * K m ≤ min (32 * w m) (w m + c₁ * K m) := le_min hA hB
      simpa using le_trans this hstepm
    · have hmj : m = j := le_antisymm hge (Nat.le_of_lt_succ hjm)
      subst hmj
      simpa using hwj

/-- The square-root branch along the whole ladder: `32^l` times the starting logarithm. -/
theorem ladder_pow (l : ℕ) (w : ℕ → ℝ)
    (hall : ∀ i, i < l → 32 * w i ≤ w (i+1)) : (32:ℝ)^l * w 0 ≤ w l := by
  induction l with
  | zero => simp
  | succ l ih =>
    have h1 : (32:ℝ)^l * w 0 ≤ w l := ih (fun i hi => hall i (Nat.lt_succ_of_lt hi))
    have h2 : 32 * w l ≤ w (l+1) := hall l (Nat.lt_succ_self l)
    calc (32:ℝ)^(l+1) * w 0 = 32 * ((32:ℝ)^l * w 0) := by ring
      _ ≤ 32 * w l := by linarith
      _ ≤ w (l+1) := h2

/-- The dichotomy of the ladder: either every rung is a power-`32` gain, in which case the
logarithm at the top is `32^l` times the one at the bottom, or some rung is an exponential gain,
in which case the logarithm at the top is at least `c₁` times the scale one rung below. -/
theorem ladder_final (l : ℕ) (w K : ℕ → ℝ) (c₁ : ℝ) (hc₁ : 0 < c₁)
    (hKpos : ∀ i, 0 < K i) (hKdouble : ∀ i, K (i+1) = 2 * K i)
    (hwnn : ∀ i, 0 ≤ w i)
    (hstep : ∀ i, i < l → min (32 * w i) (w i + c₁ * K i) ≤ w (i+1)) :
    (32:ℝ)^l * w 0 ≤ w l ∨ (0 < l ∧ c₁ * K (l-1) ≤ w l) := by
  by_cases hall : ∀ i, i < l → 32 * w i ≤ w (i+1)
  · exact Or.inl (ladder_pow l w hall)
  · right
    obtain ⟨i, hi, hlt⟩ : ∃ i, i < l ∧ w (i+1) < 32 * w i := by
      by_contra hcon
      exact hall (fun i hi => by
        by_contra h2
        exact hcon ⟨i, hi, not_le.mp h2⟩)
    have hpos : 0 < l := lt_of_le_of_lt (Nat.zero_le i) hi
    have hmin := hstep i hi
    have hother : w i + c₁ * K i ≤ w (i+1) := by
      rcases min_cases (32 * w i) (w i + c₁ * K i) with ⟨he, _⟩ | ⟨he, _⟩
      · rw [he] at hmin; exact absurd hmin (not_le.mpr hlt)
      · rw [he] at hmin; exact hmin
    have hwi : c₁ * K i ≤ w (i+1) := by linarith [hwnn i]
    refine ⟨hpos, ?_⟩
    rcases Nat.lt_or_ge (i+1) l with _hlt2 | hge2
    · exact ladder_exp l w K c₁ hc₁ hKpos hKdouble hstep i hi hwi l hi le_rfl
    · have : i + 1 = l := le_antisymm hi hge2
      rw [← this]
      simpa using hwi

/-- **Proposition 2.2 of the source in arithmetic form.**  A chain of `A` three-ball inequalities
between two scales, each of which is either an exponential gain or a square-root loss, either
contains one exponential gain, which already adds `t/2` to the logarithm of the maximum, or
consists of square-root losses only, which multiply that logarithm by `32`. -/
theorem chain_dichotomy (A : ℕ) (m : ℕ → ℝ) (C C₁ t : ℝ)
    (hC : 0 < C) (_ht : 0 < t) (hCt : 2*C ≤ Real.exp (t/2))
    (hC₁ : (2*C)^4 ≤ C₁) (hC₁1 : 1 < C₁)
    (hm0 : C₁ ≤ m 0)
    (hmono : ∀ i j, i ≤ j → j ≤ A → m i ≤ m j)
    (hA : (3/4:ℝ)^A ≤ 1/32)
    (hrung : ∀ i, i < A → m i ≤ C * Real.sqrt (m (i+1)) + C * Real.exp (-t) * m (i+1)) :
    min (32 * Real.log (m 0)) (Real.log (m 0) + t/2) ≤ Real.log (m A) := by
  have hmge : ∀ i, i ≤ A → C₁ ≤ m i := fun i hi => le_trans hm0 (hmono 0 i (Nat.zero_le i) hi)
  have hmpos : ∀ i, i ≤ A → 0 < m i := fun i hi => lt_of_lt_of_le (by linarith) (hmge i hi)
  have hm1 : ∀ i, i ≤ A → 1 ≤ m i := fun i hi => le_trans (le_of_lt hC₁1) (hmge i hi)
  have hlogbig : ∀ i, i ≤ A → 4 * Real.log (2*C) ≤ Real.log (m i) := by
    intro i hi
    have h1 : Real.log ((2*C)^4) ≤ Real.log (m i) :=
      Real.log_le_log (by positivity) (le_trans hC₁ (hmge i hi))
    rwa [Real.log_pow] at h1
    
  by_cases hall : ∀ i, i < A → m i ≤ 2 * C * Real.sqrt (m (i+1))
  · refine le_trans (min_le_left _ _) ?_
    refine log_chain_pow A (fun i => Real.log (m i)) hA
      (Real.log_nonneg (hm1 A le_rfl)) ?_
    intro i hi
    exact log_step C (m i) (m (i+1)) hC (hmpos i (le_of_lt hi))
      (hmpos (i+1) (Nat.succ_le_of_lt hi)) (hlogbig (i+1) (Nat.succ_le_of_lt hi)) (hall i hi)
  · refine le_trans (min_le_right _ _) ?_
    obtain ⟨i, hi, hne⟩ : ∃ i, i < A ∧ ¬ (m i ≤ 2 * C * Real.sqrt (m (i+1))) := by
      by_contra hcon
      exact hall (fun i hi => by
        by_contra h2
        exact hcon ⟨i, hi, h2⟩)
    have hexp : m i ≤ 2 * C * Real.exp (-t) * m (i+1) := by
      rcases tb_dichotomy C t (m i) (m (i+1)) (hrung i hi) with h | h
      · exact h
      · exact absurd h hne
    have hi1 : i + 1 ≤ A := Nat.succ_le_of_lt hi
    have hm1pos : 0 < m (i+1) := hmpos (i+1) hi1
    have hstep : Real.exp (t/2) * m i ≤ m (i+1) := by
      have h1 : 2 * C * Real.exp (-t) * m (i+1) ≤ Real.exp (t/2) * Real.exp (-t) * m (i+1) := by
        have h2 : 2 * C * Real.exp (-t) ≤ Real.exp (t/2) * Real.exp (-t) :=
          mul_le_mul_of_nonneg_right hCt (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right h2 hm1pos.le
      have h3 : Real.exp (t/2) * Real.exp (-t) = Real.exp (-(t/2)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [h3] at h1
      have h4 : m i ≤ Real.exp (-(t/2)) * m (i+1) := le_trans hexp h1
      have h5 : Real.exp (t/2) * m i ≤ Real.exp (t/2) * (Real.exp (-(t/2)) * m (i+1)) :=
        mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
      have h6 : Real.exp (t/2) * (Real.exp (-(t/2)) * m (i+1)) = m (i+1) := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
      linarith [h5, h6.le, h6.ge]
    have hlogstep : Real.log (m 0) + t/2 ≤ Real.log (m (i+1)) := by
      have h1 : Real.log (Real.exp (t/2) * m i) ≤ Real.log (m (i+1)) :=
        Real.log_le_log (mul_pos (Real.exp_pos _) (hmpos i (le_of_lt hi))) hstep
      rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (hmpos i (le_of_lt hi))), Real.log_exp] at h1
      have h2 : Real.log (m 0) ≤ Real.log (m i) :=
        Real.log_le_log (hmpos 0 (Nat.zero_le A)) (hmono 0 i (Nat.zero_le i) (le_of_lt hi))
      linarith
    exact le_trans hlogstep
      (Real.log_le_log hm1pos (hmono (i+1) A hi1 le_rfl))

