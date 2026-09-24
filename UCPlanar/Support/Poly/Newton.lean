/-
Newton interpolation in one variable: the Newton polynomial of a sequence, its
forward difference, and the discrete Taylor remainder bound.
-/
import Mathlib

open scoped BigOperators Classical
set_option autoImplicit false

/-- The degree-`m` Newton polynomial of a sequence, in the binomial basis. -/
noncomputable def newtonPoly (g : ℕ → ℝ) (m : ℕ) : ℕ → ℝ :=
  fun k => ∑ j ∈ Finset.range (m + 1), (k.choose j : ℝ) * (fwdDiff (1 : ℕ))^[j] g 0

/-- Newton's forward-difference formula: the Newton polynomial reproduces `g` on
the first `m + 1` points. -/
theorem newtonPoly_eq_of_le (g : ℕ → ℝ) (m k : ℕ) (hk : k ≤ m) :
    newtonPoly g m k = g k := by
  have h := shift_eq_sum_fwdDiff_iter (1 : ℕ) g k 0
  simp only [zero_add, nsmul_eq_mul, Nat.mul_one, Nat.cast_id] at h
  have hsub : ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (fwdDiff (1 : ℕ))^[j] g 0
      = ∑ j ∈ Finset.range (m + 1), (k.choose j : ℝ) * (fwdDiff (1 : ℕ))^[j] g 0 :=
    Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) (fun j _ hj => by
      simp only [Finset.mem_range] at hj
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul])
  rw [newtonPoly, ← hsub, ← h]

/-- The forward difference of the degree-`m + 1` Newton polynomial is the
degree-`m` Newton polynomial of the forward difference. -/
theorem fwdDiff_newtonPoly (g : ℕ → ℝ) (m : ℕ) :
    fwdDiff (1 : ℕ) (newtonPoly g (m + 1)) = newtonPoly (fwdDiff (1 : ℕ) g) m := by
  funext k
  simp only [newtonPoly, fwdDiff]
  have hsub : (∑ j ∈ Finset.range (m + 1 + 1), ((k + 1).choose j : ℝ) * (fwdDiff (1 : ℕ))^[j] g 0)
      - (∑ j ∈ Finset.range (m + 1 + 1), (k.choose j : ℝ) * (fwdDiff (1 : ℕ))^[j] g 0)
      = ∑ j ∈ Finset.range (m + 1 + 1),
          (((k + 1).choose j : ℝ) * (fwdDiff (1 : ℕ))^[j] g 0
            - (k.choose j : ℝ) * (fwdDiff (1 : ℕ))^[j] g 0) := by
    rw [Finset.sum_sub_distrib]
  rw [hsub, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, sub_self, add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Nat.choose_succ_succ', Function.iterate_succ]
  simp only [Function.comp_apply]
  push_cast
  ring
/-- The Newton polynomial of order `m + 1` differs from `g` by the sum of the
order-`m` Newton remainders of the forward difference of `g`. -/
theorem newtonPoly_sub_eq_sum (g : ℕ → ℝ) (m k : ℕ) :
    g k - newtonPoly g (m + 1) k
      = ∑ t ∈ Finset.range k,
          (fwdDiff (1 : ℕ) g t - newtonPoly (fwdDiff (1 : ℕ) g) m t) := by
  have h0 : newtonPoly g (m + 1) 0 = g 0 := newtonPoly_eq_of_le g (m + 1) 0 (Nat.zero_le _)
  have hsum := Finset.sum_range_sub (fun t => g t - newtonPoly g (m + 1) t) k
  rw [h0, sub_self, sub_zero] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  have hfd := congrFun (fwdDiff_newtonPoly g m) t
  have hfd' : newtonPoly g (m + 1) (t + 1) - newtonPoly g (m + 1) t
      = newtonPoly (fwdDiff (1 : ℕ) g) m t := hfd
  have hg : fwdDiff (1 : ℕ) g t = g (t + 1) - g t := rfl
  linarith [hfd', hg]

/-- The discrete Taylor remainder bound in one variable: the error of the
degree-`m` Newton polynomial at `k` is at most `k^(m+1)` times a bound on the
`(m+1)`-st forward difference. -/
theorem taylor_remainder_bound (g : ℕ → ℝ) (m k : ℕ) (M : ℝ)
    (hM : ∀ t, |(fwdDiff (1 : ℕ))^[m + 1] g t| ≤ M) :
    |g k - newtonPoly g m k| ≤ (k : ℝ) ^ (m + 1) * M := by
  induction m generalizing g k M with
  | zero =>
    have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
    rw [newtonPoly, Finset.range_one, Finset.sum_singleton]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Function.iterate_zero_apply]
    rw [← Finset.sum_range_sub g k]
    calc |∑ t ∈ Finset.range k, (g (t + 1) - g t)|
        ≤ ∑ t ∈ Finset.range k, |g (t + 1) - g t| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t ∈ Finset.range k, M :=
          Finset.sum_le_sum (fun t _ => by
            simpa [zero_add, Function.iterate_one, fwdDiff] using hM t)
      _ = (k : ℝ) * M := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = (k : ℝ) ^ (0 + 1) * M := by simp
  | succ m ih =>
    have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
    rw [newtonPoly_sub_eq_sum]
    calc |∑ t ∈ Finset.range k,
            (fwdDiff (1 : ℕ) g t - newtonPoly (fwdDiff (1 : ℕ) g) m t)|
        ≤ ∑ t ∈ Finset.range k,
            |fwdDiff (1 : ℕ) g t - newtonPoly (fwdDiff (1 : ℕ) g) m t| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ Finset.range k, (t : ℝ) ^ (m + 1) * M :=
          Finset.sum_le_sum (fun t _ => ih (fwdDiff (1 : ℕ) g) t M (fun s => by
            have hstep : (fwdDiff (1 : ℕ))^[m + 1] (fwdDiff (1 : ℕ) g) s
                = (fwdDiff (1 : ℕ))^[m + 1 + 1] g s := by
              rw [Function.iterate_add_apply (fwdDiff (1 : ℕ)) (m + 1) 1 g, Function.iterate_one]
            rw [hstep]
            exact hM s))
      _ ≤ (k : ℝ) ^ (m + 1 + 1) * M := by
          rw [← Finset.sum_mul]
          have hle : ∑ t ∈ Finset.range k, (t : ℝ) ^ (m + 1)
              ≤ (k : ℝ) * (k : ℝ) ^ (m + 1) := by
            calc ∑ t ∈ Finset.range k, (t : ℝ) ^ (m + 1)
                ≤ ∑ _t ∈ Finset.range k, (k : ℝ) ^ (m + 1) :=
                  Finset.sum_le_sum (fun t ht => by
                    have ht' : t ≤ k := le_of_lt (Finset.mem_range.mp ht)
                    exact pow_le_pow_left₀ (Nat.cast_nonneg t) (by exact_mod_cast ht') _)
              _ = (k : ℝ) * (k : ℝ) ^ (m + 1) := by
                  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          calc (∑ t ∈ Finset.range k, (t : ℝ) ^ (m + 1)) * M
              ≤ ((k : ℝ) * (k : ℝ) ^ (m + 1)) * M := mul_le_mul_of_nonneg_right hle hM0
            _ = (k : ℝ) ^ (m + 1 + 1) * M := by rw [pow_succ]; ring

/-- The hockey-stick identity: the sum of the binomial coefficients
`t.choose (m+1)` over `t < k` is `k.choose (m+2)`. -/
theorem sum_range_choose_succ (k m : ℕ) :
    ∑ t ∈ Finset.range k, t.choose (m + 1) = k.choose (m + 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ]
    exact Nat.add_comm _ _

theorem sum_range_choose_mul_choose (a b n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), a.choose i * b.choose (n - i) = (a + b).choose n := by
  rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- The sharp discrete Taylor remainder bound in one variable, with the bound on the
`(m+1)`-st forward difference required only at the points that the `(m+1)`-fold summation
from `0` to `k` visits: the error of the degree-`m` Newton polynomial at `k` is at most the
binomial coefficient `k.choose (m+1)` times that bound. -/
theorem taylor_remainder_bound_choose_local (g : ℕ → ℝ) (m k : ℕ) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ t, t + (m + 1) ≤ k → |(fwdDiff (1 : ℕ))^[m + 1] g t| ≤ M) :
    |g k - newtonPoly g m k| ≤ (k.choose (m + 1) : ℝ) * M := by
  induction m generalizing g k M with
  | zero =>
    rw [newtonPoly, Finset.range_one, Finset.sum_singleton]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Function.iterate_zero_apply]
    rw [← Finset.sum_range_sub g k]
    calc |∑ t ∈ Finset.range k, (g (t + 1) - g t)|
        ≤ ∑ t ∈ Finset.range k, |g (t + 1) - g t| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t ∈ Finset.range k, M :=
          Finset.sum_le_sum (fun t ht => by
            have htk : t + (0 + 1) ≤ k := by
              have := Finset.mem_range.mp ht
              omega
            simpa [zero_add, Function.iterate_one, fwdDiff] using hM t htk)
      _ = (k : ℝ) * M := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = (k.choose (0 + 1) : ℝ) * M := by simp
  | succ m ih =>
    rw [newtonPoly_sub_eq_sum]
    calc |∑ t ∈ Finset.range k,
            (fwdDiff (1 : ℕ) g t - newtonPoly (fwdDiff (1 : ℕ) g) m t)|
        ≤ ∑ t ∈ Finset.range k,
            |fwdDiff (1 : ℕ) g t - newtonPoly (fwdDiff (1 : ℕ) g) m t| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ Finset.range k, (t.choose (m + 1) : ℝ) * M :=
          Finset.sum_le_sum (fun t ht => ih (fwdDiff (1 : ℕ) g) t M hM0 (fun s hs => by
            have hstep : (fwdDiff (1 : ℕ))^[m + 1] (fwdDiff (1 : ℕ) g) s
                = (fwdDiff (1 : ℕ))^[m + 1 + 1] g s := by
              rw [Function.iterate_add_apply (fwdDiff (1 : ℕ)) (m + 1) 1 g, Function.iterate_one]
            rw [hstep]
            refine hM s ?_
            have := Finset.mem_range.mp ht
            omega))
      _ = (∑ t ∈ Finset.range k, (t.choose (m + 1) : ℝ)) * M := by rw [Finset.sum_mul]
      _ = (k.choose (m + 1 + 1) : ℝ) * M := by
          congr 1
          rw [← Nat.cast_sum, sum_range_choose_succ]
