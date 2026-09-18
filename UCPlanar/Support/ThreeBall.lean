/-
The lattice ingredients of the three-ball inequality on a periodic planar graph.

The appendix of the paper reduces the three-ball proposition to a statement about a harmonic
function on a lattice box: the cited discrete Remez inequality for polynomials, a one-dimensional
propagation along a coordinate line, a second propagation in the transverse coordinate, and a
covering argument.  This module holds the Remez input and the counting that the propagation
consumes: the half-lines lemma, which turns a density hypothesis on the box into a dense set of
lines each carrying a dense set of points, and the arithmetic of the two cases.  The propagation
itself is in ThreeLine.lean and ThreeProp.lean.
-/
import UCPlanar.Support.Approximation
import UCPlanar.Support.RemezDiscrete
import UCPlanar.Support.Density
import UCPlanar.Support.Harmonic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Polynomial.Eval.Defs

open scoped Classical
set_option autoImplicit false

namespace UCPlanar.Support.Three

/-- The lattice square `Q_N` of side length `2N+1`. -/
noncomputable def box (N : ℕ) : Finset (ℤ × ℤ) := (seg N).product (seg N)

/-- The discrete Remez inequality (Buhovsky–Logunov–Malinnikova–Sodin, Corollary 2.2,
cited at `ucplanar.tex:487`): a polynomial of degree at most `m` that is bounded by `A`
at at least half of the integer points of `[-R, R]` is bounded by
`A * (16 R / (R - m))^m` on `[-2R, 2R]`. -/
def RemezInput : Prop :=
  ∀ (R : ℝ) (m : ℕ) (A : ℝ) (p : Polynomial ℝ),
    0 ≤ A → 0 < R → (m : ℝ) < R → p.natDegree ≤ m →
    (∃ S : Finset ℤ, S ⊆ seg ⌈R⌉₊ ∧ 2 * S.card ≥ (seg ⌈R⌉₊).card ∧
      ∀ s ∈ S, |p.eval (s : ℝ)| ≤ A) →
    ∀ s : ℤ, |(s : ℝ)| ≤ 2 * R → |p.eval (s : ℝ)| ≤ A * (16 * R / (R - m)) ^ m

/-- The discrete Remez inequality holds: it is proved in `RemezDiscrete.lean`. -/
theorem remezInput : RemezInput := discreteRemez

/-- The Remez ratio is at most `64` once `γ ≤ 3/4`. -/
theorem rpow_ratio_le (γ : ℝ) (N : ℕ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 3 / 4) :
    (16 / (1 - γ)) ^ (γ * (N : ℝ)) ≤ 64 ^ (γ * (N : ℝ)) := by
  have h1 : (16 : ℝ) / (1 - γ) ≤ 64 := by rw [div_le_iff₀ (by linarith)]; linarith
  have h2 : (0 : ℝ) ≤ 16 / (1 - γ) := by apply div_nonneg <;> linarith
  exact Real.rpow_le_rpow h2 h1 (mul_nonneg hγ0 (Nat.cast_nonneg N))

theorem pow_arith (m : ℕ) : (m + 1) * 3 ^ m ≤ 16 ^ m := by
  have h1 : (m + 1 : ℕ) ≤ 3 ^ m := by
    induction m with
    | zero => norm_num
    | succ k ih =>
      rw [pow_succ]
      nlinarith [ih, Nat.zero_le k]
  have h2 : 3 ^ m * 3 ^ m ≤ 16 ^ m := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by norm_num) m
  calc (m + 1) * 3 ^ m ≤ 3 ^ m * 3 ^ m := Nat.mul_le_mul_right _ h1
    _ ≤ 16 ^ m := h2

theorem basis_bound (m : ℕ) (R : ℝ)
    (x : Fin (m+1) → ℤ) (hinj : Function.Injective x) (hx : ∀ i, |(x i : ℝ)| ≤ R)
    (s : ℤ) (hs : |(s : ℝ)| ≤ 2*R) (i : Fin (m+1)) :
    |(Lagrange.basis Finset.univ (fun i : Fin (m+1) => (x i : ℝ)) i).eval (s : ℝ)|
      ≤ (3*R)^m := by
  rw [Lagrange.basis, Polynomial.eval_prod]
  have hfac : ∀ j ∈ Finset.univ.erase i,
      |Polynomial.eval (s : ℝ) (Lagrange.basisDivisor ((x i : ℝ)) ((x j : ℝ)))| ≤ 3 * R := by
    intro j hj
    rw [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    have h1 : |(s : ℝ) - (x j : ℝ)| ≤ 3 * R := by
      rw [abs_le]
      constructor <;>
        linarith [le_abs_self (s : ℝ), neg_le_abs (s : ℝ), le_abs_self (x j : ℝ),
          neg_le_abs (x j : ℝ), hs, hx j]
    have h2 : (1 : ℝ) ≤ |(x i : ℝ) - (x j : ℝ)| := by
      have hne : x i ≠ x j := fun h => (Finset.mem_erase.mp hj).1 (hinj h).symm
      have hne' : x i - x j ≠ 0 := sub_ne_zero.mpr hne
      have h3 : (1 : ℤ) ≤ |x i - x j| := by
        rcases lt_trichotomy (x i - x j) 0 with hlt | heq | hgt
        · rw [abs_of_neg hlt]; omega
        · exact absurd heq hne'
        · rw [abs_of_pos hgt]; omega
      have h4 : ((1 : ℤ) : ℝ) ≤ ((|x i - x j| : ℤ) : ℝ) := by exact_mod_cast h3
      rw [Int.cast_abs, Int.cast_sub] at h4
      simpa using h4
    rw [abs_mul, abs_inv]
    have hinv : |(x i : ℝ) - (x j : ℝ)|⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h2
    calc |(x i : ℝ) - (x j : ℝ)|⁻¹ * |(s : ℝ) - (x j : ℝ)|
        ≤ 1 * |(s : ℝ) - (x j : ℝ)| := mul_le_mul_of_nonneg_right hinv (abs_nonneg _)
      _ = |(s : ℝ) - (x j : ℝ)| := one_mul _
      _ ≤ 3 * R := h1
  calc |∏ j ∈ Finset.univ.erase i,
        Polynomial.eval (s : ℝ) (Lagrange.basisDivisor ((x i : ℝ)) ((x j : ℝ)))|
      = ∏ j ∈ Finset.univ.erase i,
          |Polynomial.eval (s : ℝ) (Lagrange.basisDivisor ((x i : ℝ)) ((x j : ℝ)))| :=
        Finset.abs_prod _ _
    _ ≤ ∏ j ∈ Finset.univ.erase i, (3 * R) :=
        Finset.prod_le_prod (fun j hj => abs_nonneg _) hfac
    _ = (3 * R) ^ (Finset.univ.erase i).card := Finset.prod_const _
    _ ≤ (3 * R) ^ m := by
        have hcard : (Finset.univ.erase i).card = m := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
          omega
        rw [hcard]

theorem remez_bound (m : ℕ) (A R : ℝ) (p : Polynomial ℝ)
    (hA : 0 ≤ A) (hR : 0 < R) (hdeg : p.natDegree ≤ m)
    (x : Fin (m+1) → ℤ) (hinj : Function.Injective x) (hx : ∀ i, |(x i : ℝ)| ≤ R)
    (hval : ∀ i, |p.eval (x i : ℝ)| ≤ A) :
    ∀ s : ℤ, |(s : ℝ)| ≤ 2*R → |p.eval (s : ℝ)| ≤ A * (16*R)^m := by
  intro s hs
  have hkey : p = Lagrange.interpolate Finset.univ (fun i : Fin (m+1) => (x i : ℝ))
      (fun i => p.eval (x i : ℝ)) := by
    apply Lagrange.eq_interpolate
    · intro i _ j _ h
      exact hinj (Int.cast_injective h)
    · rw [Finset.card_univ, Fintype.card_fin]
      rcases eq_or_ne p 0 with hp | hp
      · rw [hp, Polynomial.degree_zero]
        exact WithBot.bot_lt_coe _
      · rw [← Polynomial.natDegree_lt_iff_degree_lt (n := m+1) hp]
        omega
  have h2 : p.eval (s : ℝ) = ∑ i, p.eval (x i : ℝ) *
      (Lagrange.basis Finset.univ (fun i : Fin (m+1) => (x i : ℝ)) i).eval (s : ℝ) := by
    conv_lhs => rw [hkey]
    rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [h2]
  calc |∑ i, p.eval (x i : ℝ) *
        (Lagrange.basis Finset.univ (fun i : Fin (m+1) => (x i : ℝ)) i).eval (s : ℝ)|
      ≤ ∑ i, |p.eval (x i : ℝ) *
        (Lagrange.basis Finset.univ (fun i : Fin (m+1) => (x i : ℝ)) i).eval (s : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (m+1), A * (3*R)^m := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hval i) (basis_bound m R x hinj hx s hs i) (abs_nonneg _) hA
    _ = ((m+1 : ℕ) : ℝ) * (A * (3*R)^m) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ A * (16*R)^m := by
        have hR0 : 0 ≤ R := hR.le
        have h3 : (3*R)^m = 3^m * R^m := by rw [mul_pow]
        have h16 : (16*R)^m = 16^m * R^m := by rw [mul_pow]
        rw [h3, h16]
        have hpa : ((m+1 : ℕ) : ℝ) * (3:ℝ)^m ≤ (16:ℝ)^m := by
          exact_mod_cast pow_arith m
        have hRm : 0 ≤ R^m := pow_nonneg hR0 m
        have hstep : ((m+1 : ℕ) : ℝ) * (3:ℝ)^m * (A * R^m) ≤ (16:ℝ)^m * (A * R^m) :=
          mul_le_mul_of_nonneg_right hpa (mul_nonneg hA hRm)
        nlinarith [hstep]


/-- Case 2 of the one-dimensional propagation: the outer bound `M exp(βN) > 1` gives
the exponential decay rate `exp(-(log 32)/2 · N)`. -/
theorem case2_arith (β M : ℝ) (hβ : β = -Real.log 32) (hM : 0 < M)
    (h : 1 < M * Real.exp (β * 1)) :
    (2 * (M * Real.exp (β * 1)) * 32 ^ ((1 : ℝ) / 2) + M * Real.exp (β * 1))
      ≤ 3 * Real.exp (-(Real.log 32 / 2) * 1) * M := by
  rw [hβ] at h ⊢
  have h32 : (32 : ℝ) ^ ((1 : ℝ) / 2) ≤ 6 := by
    rw [← Real.sqrt_eq_rpow]
    rw [show (32 : ℝ) = 16 * 2 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
    rw [show Real.sqrt 16 = 4 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2,
      sq_nonneg (Real.sqrt 2 - 3 / 2)]
  have hexp : Real.exp (-Real.log 32 * 1) = 1 / 32 := by
    rw [show -Real.log 32 * 1 = -Real.log 32 by ring, Real.exp_neg,
      Real.exp_log (by norm_num : (0 : ℝ) < 32)]
    norm_num
  have hexp2 : (1 : ℝ) / 6 ≤ Real.exp (-(Real.log 32 / 2) * 1) := by
    rw [show -(Real.log 32 / 2) * 1 = -(Real.log 32 / 2) by ring]
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 1 / 6)]
    rw [Real.exp_le_exp]
    have hlog : Real.log 32 / 2 = Real.log ((32 : ℝ) ^ ((1 : ℝ) / 2)) := by
      rw [Real.log_rpow (by norm_num : (0 : ℝ) < 32)]
      ring
    rw [hlog]
    rw [show Real.log (1 / 6) = -Real.log 6 by
      rw [show (1 : ℝ) / 6 = 6⁻¹ by norm_num, Real.log_inv]]
    rw [neg_le_neg_iff]
    exact Real.log_le_log (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 32) ((1 : ℝ) / 2)) h32
  nlinarith [h, hM, hexp, hexp2, h32]


/-- The covering step: a box of side `kN` with `k ≥ 4` contains the square `Q_{4N}`. -/
theorem cover_arith (k N : ℕ) (hk : 4 ≤ k) : (4 * N : ℕ) ≤ k * N :=
  Nat.mul_le_mul_right N hk


/-- The density hypothesis on a line gives a half-density subset on which `|f| ≤ 1`. -/
theorem density_transfer (N : ℕ) (ε : ℝ) (f : ℤ → ℤ → ℝ)
    (_hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hdens : (1 - ε) * ((seg N).card : ℝ) ≤
      (((seg N).filter (fun s => |f s 0| ≤ 1)).card : ℝ)) :
    ∃ S : Finset ℤ, S ⊆ seg N ∧ 2 * S.card ≥ (seg N).card ∧ ∀ s ∈ S, |f s 0| ≤ 1 := by
  refine ⟨(seg N).filter (fun s => |f s 0| ≤ 1), ?_, ?_, ?_⟩
  · exact Finset.filter_subset _ _
  · have h2 : (1 / 2 : ℝ) ≤ 1 - ε := by linarith [hε1]
    have h3 : (1 / 2 : ℝ) * ((seg N).card : ℝ) ≤ (((seg N).filter (fun s => |f s 0| ≤ 1)).card : ℝ) := by
      have h4 : (0 : ℝ) ≤ ((seg N).card : ℝ) := Nat.cast_nonneg _
      nlinarith [hdens, h2, h4]
    have h5 : ((seg N).card : ℝ) ≤ 2 * (((seg N).filter (fun s => |f s 0| ≤ 1)).card : ℝ) := by linarith
    exact_mod_cast h5
  · intro s hs
    exact (Finset.mem_filter.mp hs).2


theorem remez_half (N : ℕ) (hN : 0 < N) (hremez : RemezInput) (p : Polynomial ℝ)
    (hdeg : p.natDegree ≤ N/2)
    (hS : ∃ S : Finset ℤ, S ⊆ seg N ∧ 2 * S.card ≥ (seg N).card ∧ ∀ s ∈ S, |p.eval (s:ℝ)| ≤ 2)
    (s : ℤ) (hs : |(s:ℝ)| ≤ 2*(N:ℝ)) :
    |p.eval (s:ℝ)| ≤ 2 * 32 ^ ((N:ℝ)/2) := by
  obtain ⟨S, hSsub, hScard, hSval⟩ := hS
  have hR : (0:ℝ) < N := by exact_mod_cast hN
  have hm : ((N/2 : ℕ) : ℝ) < (N:ℝ) := by
    have : N/2 < N := Nat.div_lt_self hN (by norm_num)
    exact_mod_cast this
  have hceil : ⌈(N:ℝ)⌉₊ = N := by simp
  have h := hremez (N:ℝ) (N/2) 2 p (by norm_num) hR hm hdeg
    ⟨S, by rwa [hceil], by rwa [hceil], hSval⟩ s hs
  have hratio : 16 * (N:ℝ) / ((N:ℝ) - ((N/2 : ℕ):ℝ)) ≤ 32 := by
    have h1 : ((N/2 : ℕ):ℝ) ≤ (N:ℝ) - ((N/2 : ℕ):ℝ) := by
      have : 2 * (N/2) ≤ N := Nat.mul_div_le N 2
      have h2 : (2 * (N/2) : ℕ) ≤ N := this
      have h3 : (2:ℝ) * ((N/2 : ℕ):ℝ) ≤ (N:ℝ) := by exact_mod_cast h2
      linarith
    have h4 : (0:ℝ) < (N:ℝ) - ((N/2 : ℕ):ℝ) := by
      have hlt : N/2 < N := Nat.div_lt_self hN (by norm_num)
      have hlt' : ((N/2 : ℕ):ℝ) < (N:ℝ) := by exact_mod_cast hlt
      linarith
    rw [div_le_iff₀ h4]
    nlinarith [h1]
  have hpow : (16 * (N:ℝ) / ((N:ℝ) - ((N/2 : ℕ):ℝ))) ^ (N/2) ≤ 32 ^ (N/2) :=
    pow_le_pow_left₀ (by positivity) hratio (N/2)
  have h32 : (32:ℝ) ^ (N/2) ≤ 32 ^ ((N:ℝ)/2) := by
    rw [← Real.rpow_natCast 32 (N/2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 32)
    have hdiv : ((N/2 : ℕ):ℝ) * 2 ≤ (N:ℝ) := by
      have := Nat.div_mul_le_self N 2
      exact_mod_cast this
    linarith
  linarith [h, hpow, h32]

/-- Case-2 arithmetic: `β = -log 32` and `δ = M exp(βN) > 1` give
`32^{N/2} · 2δ + exp(βN) M ≤ 3 exp(-(log 32 / 2) N) M`. -/
theorem prop1d_case2_arith (β M : ℝ) (N : ℕ) (hβ : β = -Real.log 32) (hM : 0 < M)
    (hcase : 1 < M * Real.exp (β * (N:ℝ))) :
    32 ^ ((N:ℝ)/2) * (2 * (M * Real.exp (β * (N:ℝ)))) + Real.exp (β * (N:ℝ)) * M
      ≤ 3 * Real.exp (-(Real.log 32 / 2) * (N:ℝ)) * M := by
  subst hβ
  have h32 : (32:ℝ) ^ ((N:ℝ)/2) = Real.exp (Real.log 32 * ((N:ℝ)/2)) := Real.rpow_def_of_pos (by norm_num) _
  rw [h32]
  have hlog : 0 < Real.log 32 := Real.log_pos (by norm_num)
  have hN : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hexp : Real.exp (Real.log 32 * ((N:ℝ)/2)) * Real.exp (-(Real.log 32) * (N:ℝ)) = Real.exp (-(Real.log 32 / 2) * (N:ℝ)) := by
    rw [← Real.exp_add, Real.exp_eq_exp]
    ring
  have hle : Real.exp (-(Real.log 32) * (N:ℝ)) ≤ Real.exp (-(Real.log 32 / 2) * (N:ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hlog, hN]
  nlinarith [hexp, hle, hM, Real.exp_pos (-(Real.log 32 / 2) * (N:ℝ)), Real.exp_pos (-(Real.log 32) * (N:ℝ)), Real.exp_pos (Real.log 32 * ((N:ℝ) / 2))]

/-- The fiberwise sum over the box splits along a subset of the lines. -/
theorem sum_split (N : ℕ) (f : ℤ → ℤ → ℝ) (T : Finset ℤ) (hTsub : T ⊆ seg N) :
    (∑ t ∈ seg N, ((seg N).filter (fun s => |f s t| ≤ 1)).card)
      = (∑ t ∈ T, ((seg N).filter (fun s => |f s t| ≤ 1)).card)
      + (∑ t ∈ seg N \ T, ((seg N).filter (fun s => |f s t| ≤ 1)).card) := by
  rw [← Finset.sum_sdiff hTsub]
  ring

/-- The counting arithmetic of the half-lines step: with `n = (seg N).card`, a
`(1-ε)`-density set with `ε ≤ 1/4` forces `2 T.card ≥ n`. -/
theorem half_lines_arith (n k : ℕ) (ε : ℝ) (hn : 1 ≤ n) (hk : k ≤ n) (hε : ε ≤ 1/4)
    (hkey : (1 - ε) * ((n:ℝ) * n) ≤ (k:ℝ) * n + ((n - k : ℕ) : ℝ) * (((n - 1) / 2 : ℕ) : ℝ)) :
    2 * k ≥ n := by
  have hcast : ((n - k : ℕ) : ℝ) = (n:ℝ) - (k:ℝ) := by rw [Nat.cast_sub hk]
  have hhalf : (((n - 1) / 2 : ℕ) : ℝ) ≤ ((n:ℝ) - 1) / 2 := by
    have h1 : ((n - 1 : ℕ) : ℝ) = (n:ℝ) - 1 := by rw [Nat.cast_sub hn]; norm_num
    have h2 : (((n - 1) / 2 : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) / 2 := by
      rw [le_div_iff₀ (by norm_num)]
      exact_mod_cast Nat.div_mul_le_self (n - 1) 2
    rw [h1] at h2; linarith
  rw [hcast] at hkey
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hk1 : (k:ℝ) ≤ n := by exact_mod_cast hk
  have hmain : (n:ℝ) ≤ 2 * (k:ℝ) := by nlinarith [hkey, hε, hn1, hhalf, hk1]
  exact_mod_cast hmain

/-- The half-lines step of the three-ball proof: a `(1-ε)`-density set of points with
`|f| ≤ 1` in the box, `ε ≤ 1/4`, contains half of the lines, each of which contains half of
its points with `|f| ≤ 1`. -/
theorem half_lines (N : ℕ) (f : ℤ → ℤ → ℝ) (ε : ℝ) (hε : ε ≤ 1/4)
    (hdens : (1 - ε) * ((box N).card : ℝ) ≤
      (((box N).filter (fun x => |f x.1 x.2| ≤ 1)).card : ℝ)) :
    ∃ T : Finset ℤ, T ⊆ seg N ∧ 2 * T.card ≥ (seg N).card ∧
      ∀ t ∈ T, ∃ S : Finset ℤ, S ⊆ seg N ∧ 2 * S.card ≥ (seg N).card ∧
        ∀ s ∈ S, |f s t| ≤ 1 := by
  classical
  set G : Finset (ℤ × ℤ) := (box N).filter (fun x => |f x.1 x.2| ≤ 1) with hG
  set T : Finset ℤ := (seg N).filter (fun t => 2 * ((seg N).filter (fun s => |f s t| ≤ 1)).card ≥ (seg N).card) with hT
  have hbox : box N = (seg N).product (seg N) := rfl
  have hsum : G.card = ∑ t ∈ seg N, ((seg N).filter (fun s => |f s t| ≤ 1)).card := by
    rw [hG, hbox, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [show (seg N).product (seg N) = seg N ×ˢ seg N from rfl, Finset.sum_product]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hboxcard : (box N).card = (seg N).card * (seg N).card := by
    rw [hbox, show (seg N).product (seg N) = seg N ×ˢ seg N from rfl, Finset.card_product]
  have hTsub : T ⊆ seg N := by intro t ht; rw [hT] at ht; exact (Finset.mem_filter.mp ht).1
  have hTval : ∀ t ∈ T, 2 * ((seg N).filter (fun s => |f s t| ≤ 1)).card ≥ (seg N).card := by
    intro t ht; rw [hT] at ht; exact (Finset.mem_filter.mp ht).2
  have hnotT : ∀ t ∈ seg N, t ∉ T → 2 * ((seg N).filter (fun s => |f s t| ≤ 1)).card < (seg N).card := by
    intro t ht hnt
    by_contra hcon
    exact hnt (by rw [hT]; exact Finset.mem_filter.mpr ⟨ht, le_of_not_gt hcon⟩)
  refine ⟨T, hTsub, ?_, ?_⟩
  · set n : ℕ := (seg N).card with hn
    have hnpos : 0 < n := by
      rw [hn]
      exact Finset.card_pos.mpr ⟨0, by simp [seg]⟩
    have hsplit := sum_split N f T hTsub
    have hTle : ∑ t ∈ T, ((seg N).filter (fun s => |f s t| ≤ 1)).card ≤ T.card * n := by
      calc ∑ t ∈ T, ((seg N).filter (fun s => |f s t| ≤ 1)).card
          ≤ ∑ _t ∈ T, n := Finset.sum_le_sum fun t _ => by
            rw [hn]; exact Finset.card_le_card (Finset.filter_subset _ _)
        _ = T.card * n := by rw [Finset.sum_const, smul_eq_mul]
    have hnotle : ∑ t ∈ seg N \ T, ((seg N).filter (fun s => |f s t| ≤ 1)).card
        ≤ ((seg N \ T).card) * ((n - 1) / 2) := by
      calc ∑ t ∈ seg N \ T, ((seg N).filter (fun s => |f s t| ≤ 1)).card
          ≤ ∑ _t ∈ seg N \ T, ((n - 1) / 2) := Finset.sum_le_sum fun t ht => by
            have ht' : t ∈ seg N := (Finset.mem_sdiff.mp ht).1
            have hnt : t ∉ T := (Finset.mem_sdiff.mp ht).2
            have hlt := hnotT t ht' hnt
            omega
        _ = ((seg N \ T).card) * ((n - 1) / 2) := by rw [Finset.sum_const, smul_eq_mul]
    have hsdiff : (seg N \ T).card = n - T.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hTsub, hn]
    have hdens' : (1 - ε) * ((n:ℝ) * (n:ℝ)) ≤ (G.card : ℝ) := by
      have h1 : ((box N).card : ℝ) = (n:ℝ) * (n:ℝ) := by rw [hboxcard]; push_cast; ring
      rw [← h1]; exact hdens
    have hGle : (G.card : ℝ) ≤ (T.card : ℝ) * n + ((n - T.card : ℕ) : ℝ) * (((n - 1) / 2 : ℕ) : ℝ) := by
      have hsum' : (G.card : ℝ) = ((∑ t ∈ T, ((seg N).filter (fun s => |f s t| ≤ 1)).card : ℕ) : ℝ)
          + ((∑ t ∈ seg N \ T, ((seg N).filter (fun s => |f s t| ≤ 1)).card : ℕ) : ℝ) := by
        rw [hsum, hsplit]; push_cast; ring
      rw [hsum']
      have h1 : ((∑ t ∈ T, ((seg N).filter (fun s => |f s t| ≤ 1)).card : ℕ) : ℝ) ≤ (T.card : ℝ) * n := by exact_mod_cast hTle
      have h2 : ((∑ t ∈ seg N \ T, ((seg N).filter (fun s => |f s t| ≤ 1)).card : ℕ) : ℝ) ≤ ((seg N \ T).card : ℝ) * (((n - 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hnotle
      rw [hsdiff] at h2
      push_cast at h1 h2 ⊢
      linarith
    have hkey : (1 - ε) * ((n:ℝ) * n) ≤ (T.card : ℝ) * n + ((n - T.card : ℕ) : ℝ) * (((n - 1) / 2 : ℕ) : ℝ) := le_trans hdens' hGle
    have hk : T.card ≤ n := by rw [hn]; exact Finset.card_le_card hTsub
    exact half_lines_arith n T.card ε (by omega) hk hε hkey
  · intro t ht
    exact ⟨(seg N).filter (fun s => |f s t| ≤ 1), Finset.filter_subset _ _,
      hTval t ht, fun s hs => (Finset.mem_filter.mp hs).2⟩

/-- The covering step: the density hypothesis on the box and the bound on the box give the
half-lines data of the core, by the half-lines counting lemma. -/
theorem cover_step_density (N : ℕ) (f : ℤ → ℤ → ℝ) (ε : ℝ) (hε : ε ≤ 1/4)
    (hdens : (1 - ε) * ((box N).card : ℝ) ≤
      (((box N).filter (fun x => |f x.1 x.2| ≤ 1)).card : ℝ)) :
    ∃ T : Finset ℤ, T ⊆ seg N ∧ 2 * T.card ≥ (seg N).card ∧
      ∀ t ∈ T, ∃ S : Finset ℤ, S ⊆ seg N ∧ 2 * S.card ≥ (seg N).card ∧
        ∀ s ∈ S, |f s t| ≤ 1 :=
  half_lines N f ε hε hdens
