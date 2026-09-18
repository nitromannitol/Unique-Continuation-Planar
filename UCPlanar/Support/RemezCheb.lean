import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-!
# Chebyshev polynomial estimates for the Remez inequality

Auxiliary facts about the Chebyshev polynomials `T ℝ n`: the explicit value on `[1, ∞)`
via `arcosh`, monotonicity and the elementary bound `T_n(x) ≤ (2x)^n` there, and the
equioscillation nodes `cos((n − k)π/n)`.
-/

namespace UCPlanar.Support

open Polynomial Real Set
open Polynomial.Chebyshev

/-- The value of `T_n` on `[1, ∞)` in terms of `cosh` and `arcosh`. -/
theorem eval_chebT_eq_cosh (n : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (T ℝ (n : ℤ)).eval x = Real.cosh (n * Real.arcosh x) := by
  conv_lhs => rw [← Real.cosh_arcosh hx, T_real_cosh]
  norm_cast

/-- `T_n` is monotone on `[1, ∞)`. -/
theorem chebT_monotoneOn_one (n : ℕ) :
    MonotoneOn (fun x ↦ (T ℝ (n : ℤ)).eval x) (Set.Ici 1) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  show (T ℝ (n : ℤ)).eval x ≤ (T ℝ (n : ℤ)).eval y
  rw [eval_chebT_eq_cosh n hx, eval_chebT_eq_cosh n hy, Real.cosh_le_cosh,
    abs_of_nonneg (by positivity [Real.arcosh_nonneg hx]),
    abs_of_nonneg (by positivity [Real.arcosh_nonneg hy])]
  exact mul_le_mul_of_nonneg_left ((Real.arcosh_le_arcosh (by linarith)
    (by linarith)).mpr hxy) (by positivity)

/-- The elementary bound `T_n(x) ≤ (2x)^n` for `x ≥ 1`. -/
theorem chebT_eval_le (n : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (T ℝ (n : ℤ)).eval x ≤ (2 * x) ^ n := by
  rw [eval_chebT_eq_cosh n hx]
  set θ := Real.arcosh x with hθ
  have hθ0 : 0 ≤ θ := Real.arcosh_nonneg hx
  calc Real.cosh (n * θ) ≤ Real.exp (n * θ) := by
        rw [Real.cosh_eq]
        have h1 : Real.exp (-(n * θ)) ≤ Real.exp (n * θ) :=
          Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ n) hθ0])
        have h2 := Real.exp_pos (n * θ)
        linarith
    _ = (Real.exp θ) ^ n := by rw [← Real.exp_nat_mul]
    _ = (x + √(x ^ 2 - 1)) ^ n := by rw [Real.exp_arcosh hx]
    _ ≤ (2 * x) ^ n := by
        apply pow_le_pow_left₀ (by positivity)
        have h3 : √(x ^ 2 - 1) ≤ x := by
          calc √(x ^ 2 - 1) ≤ √(x ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
            _ = x := Real.sqrt_sq (by linarith)
        linarith

/-- The equioscillation nodes of `T_n`: `η_k = cos((n − k)π/n)` for `k ≤ n`. -/
noncomputable def chebNode (n k : ℕ) : ℝ := Real.cos (((n - k : ℕ) : ℝ) * π / n)

theorem chebNode_zero {n : ℕ} (hn : n ≠ 0) : chebNode n 0 = -1 := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [chebNode, Nat.sub_zero, mul_div_cancel_left₀ _ hnR, Real.cos_pi]

theorem chebNode_self (n : ℕ) : chebNode n n = 1 := by
  simp [chebNode]

theorem chebNode_mem_Icc (n k : ℕ) : chebNode n k ∈ Set.Icc (-1) 1 :=
  Real.cos_mem_Icc _

/-- The nodes are strictly increasing in `k` for `k ≤ n`. -/
theorem chebNode_lt_chebNode {n : ℕ} (hn : n ≠ 0) {j k : ℕ} (hj : j ≤ n) (hjk : k < j) :
    chebNode n k < chebNode n j := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hsub : ((n - j : ℕ) : ℝ) < (n - k : ℕ) := by
    have h : n - j < n - k := by omega
    exact_mod_cast h
  apply Real.cos_lt_cos_of_nonneg_of_le_pi
  · positivity
  · rw [div_le_iff₀ hnR]
    have hle : ((n - k : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n k
    calc ((n - k : ℕ) : ℝ) * π ≤ (n : ℝ) * π :=
          mul_le_mul_of_nonneg_right hle (by positivity)
      _ = π * n := by ring
  · exact (div_lt_div_iff_of_pos_right hnR).mpr (mul_lt_mul_of_pos_right hsub Real.pi_pos)

/-- The equioscillation values: `T_n(η_k) = (−1)^(n−k)`. -/
theorem eval_chebT_chebNode {n : ℕ} (hn : n ≠ 0) {k : ℕ} (_hk : k ≤ n) :
    (T ℝ (n : ℤ)).eval (chebNode n k) = (-1 : ℝ) ^ (n - k) := by
  rw [chebNode, eval_T_real_cos_int_mul_pi_div (n := n) (k := n - k) hn,
    Int.cast_negOnePow_natCast]

end UCPlanar.Support
