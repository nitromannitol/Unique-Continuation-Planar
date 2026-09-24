/-
The factorial gain in the discrete Taylor remainder: the binomial coefficient of the
sharp remainder absorbs the factor `m` that the derivative bound loses at each order.
-/
import Mathlib

open scoped BigOperators Classical
set_option autoImplicit false

namespace UCPlanar.Support

/-- `n ^ n` exceeds `n !` by at most `3 ^ n`, read off the exponential series at `n`. -/
theorem pow_self_le_three_pow_mul_factorial (n : ℕ) :
    (n : ℝ) ^ n ≤ 3 ^ n * (n.factorial : ℝ) := by
  have hfac : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hnn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hsum := Real.sum_le_exp_of_nonneg hnn (n + 1)
  have hmem : n ∈ Finset.range (n + 1) := Finset.self_mem_range_succ n
  have hsingle : (n:ℝ) ^ n / (n.factorial : ℝ)
      ≤ ∑ i ∈ Finset.range (n + 1), (n:ℝ) ^ i / (i.factorial : ℝ) :=
    Finset.single_le_sum (f := fun i => (n:ℝ) ^ i / (i.factorial : ℝ))
      (fun i _ => by positivity) hmem
  have hterm : (n:ℝ) ^ n / (n.factorial : ℝ) ≤ Real.exp (n:ℝ) := le_trans hsingle hsum
  have he1 : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
  have hexp : Real.exp (n:ℝ) ≤ 3 ^ n := by
    have h : Real.exp (n:ℝ) = Real.exp 1 ^ n := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h]
    exact pow_le_pow_left₀ (Real.exp_nonneg 1) he1 n
  rw [div_le_iff₀ hfac] at hterm
  nlinarith [hterm, hexp, hfac]

/-- The sharp remainder beats the derivative bound: the binomial coefficient `N.choose t`
against the `t`-th power of `A * t` costs only the `t`-th power of `3 * A * N`.  This is the
arithmetic that makes the polynomial approximation converge, since the derivative bound at
order `t` carries the factor `t` inside the power. -/
theorem choose_mul_pow_le (N t : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    (N.choose t : ℝ) * (A * t) ^ t ≤ (3 * A * N) ^ t := by
  have hfac : (0:ℝ) < (t.factorial : ℝ) := by exact_mod_cast t.factorial_pos
  have hch : (N.choose t : ℝ) ≤ (N : ℝ) ^ t / (t.factorial : ℝ) := Nat.choose_le_pow_div t N
  have hkk : (t : ℝ) ^ t ≤ 3 ^ t * (t.factorial : ℝ) :=
    UCPlanar.Support.pow_self_le_three_pow_mul_factorial t
  have hAt : (0:ℝ) ≤ A ^ t := pow_nonneg hA t
  have hNt : (0:ℝ) ≤ (N : ℝ) ^ t := pow_nonneg (Nat.cast_nonneg N) t
  have e1 : (A * (t:ℝ)) ^ t = A ^ t * (t:ℝ) ^ t := mul_pow A (t:ℝ) t
  have e2 : (3 * A * (N:ℝ)) ^ t = 3 ^ t * A ^ t * (N:ℝ) ^ t := by
    rw [mul_pow, mul_pow]
  rw [e1, e2]
  have h1 : (N.choose t : ℝ) * (A ^ t * (t:ℝ) ^ t)
      ≤ ((N : ℝ) ^ t / (t.factorial : ℝ)) * (A ^ t * (t:ℝ) ^ t) :=
    mul_le_mul_of_nonneg_right hch (by positivity)
  refine le_trans h1 ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ hfac]
  have h2 : (N:ℝ) ^ t * (A ^ t * (t:ℝ) ^ t)
      ≤ (N:ℝ) ^ t * (A ^ t * (3 ^ t * (t.factorial : ℝ))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkk hAt) hNt
  refine le_trans h2 (le_of_eq ?_)
  ring

end UCPlanar.Support
