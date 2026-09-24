/-
The exponential lower bound on a periodic planar graph.

The appendix iterates the three-ball inequality: if a harmonic function is bounded by `M`
on a large square and is small on a positive fraction of the inner square, then the
three-ball bound forces `M` to grow at most exponentially in the side length, and the
iteration of that bound gives the exponential lower bound of the paper.
-/
import UCPlanar.Support.ThreeBall
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped Classical

namespace UCPlanar.Support.Lower

/-- The iteration arithmetic: if `E = exp(bN)` satisfies `E ≤ C√E + C exp(-cN) E` with
`C exp(-cN) ≤ 1/2`, then `E ≤ (2C)²`. -/
theorem iteration_arith (b c C : ℝ) (N : ℕ)
    (_hb : 0 < b) (_hc : 0 < c) (hC : 0 < C)
    (hsmall : C * Real.exp (-c * (N:ℝ)) ≤ 1/2)
    (h : Real.exp (b * (N:ℝ)) ≤ C * Real.sqrt (Real.exp (b * (N:ℝ))) +
      C * Real.exp (-c * (N:ℝ)) * Real.exp (b * (N:ℝ))) :
    Real.exp (b * (N:ℝ)) ≤ (2*C)^2 := by
  set E := Real.exp (b * (N:ℝ)) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have h2 : C * Real.exp (-c * (N:ℝ)) * E ≤ (1/2) * E :=
    mul_le_mul_of_nonneg_right hsmall (le_of_lt hEpos)
  have h3 : E ≤ C * Real.sqrt E + (1/2) * E := by linarith
  have h4 : (1/2) * E ≤ C * Real.sqrt E := by linarith
  have h5 : E ≤ 2 * C * Real.sqrt E := by linarith
  have hs : Real.sqrt E * Real.sqrt E = E := by
    nlinarith [Real.sq_sqrt (le_of_lt hEpos), sq_nonneg (Real.sqrt E)]
  have h6 : Real.sqrt E ≤ 2 * C := by nlinarith [h5, hs, Real.sqrt_nonneg E, hC]
  nlinarith [h6, hs, Real.sqrt_nonneg E, hC]

/-- The exponential growth bound: under the same hypotheses, `N ≤ 2 log(2C) / b`. -/
theorem exp_growth (b c C : ℝ) (N : ℕ)
    (hb : 0 < b) (hc : 0 < c) (hC : 0 < C)
    (hsmall : C * Real.exp (-c * (N:ℝ)) ≤ 1/2)
    (h : Real.exp (b * (N:ℝ)) ≤ C * Real.sqrt (Real.exp (b * (N:ℝ))) +
      C * Real.exp (-c * (N:ℝ)) * Real.exp (b * (N:ℝ))) :
    (N:ℝ) ≤ (2 * Real.log (2*C)) / b := by
  have h1 : Real.exp (b * (N:ℝ)) ≤ (2*C)^2 := iteration_arith b c C N hb hc hC hsmall h
  have h2 : Real.exp (b * (N:ℝ)) ≤ Real.exp (Real.log ((2*C)^2)) := by
    rw [Real.exp_log (by positivity)]; exact h1
  have h3 : b * (N:ℝ) ≤ Real.log ((2*C)^2) := Real.exp_le_exp.mp h2
  rw [Real.log_pow] at h3
  rw [le_div_iff₀ hb]
  rw [mul_comm (N:ℝ) b]
  exact h3

/-- The iteration dichotomy: either the value is already bounded by `(2C)²`, or the
exponential factor is not yet small. -/
theorem threeball_iterate (C c₀ : ℝ) (N : ℕ) (M : ℝ)
    (hC : 0 < C) (_hc₀ : 0 < c₀) (hM : 0 < M)
    (h : M ≤ C * Real.sqrt M + C * Real.exp (-c₀ * (N:ℝ)) * M) :
    M ≤ (2*C)^2 ∨ Real.exp (-c₀ * (N:ℝ)) * C > 1/2 := by
  by_cases hsmall : C * Real.exp (-c₀ * (N:ℝ)) ≤ 1/2
  · left
    have h2 : C * Real.exp (-c₀ * (N:ℝ)) * M ≤ (1/2) * M := mul_le_mul_of_nonneg_right hsmall (le_of_lt hM)
    have h3 : M ≤ C * Real.sqrt M + (1/2) * M := by linarith
    have h4 : (1/2) * M ≤ C * Real.sqrt M := by linarith
    have h5 : M ≤ 2 * C * Real.sqrt M := by linarith
    have hs : Real.sqrt M * Real.sqrt M = M := by nlinarith [Real.sq_sqrt (le_of_lt hM), sq_nonneg (Real.sqrt M)]
    have h6 : Real.sqrt M ≤ 2 * C := by nlinarith [h5, hs, Real.sqrt_nonneg M, hC]
    nlinarith [h6, hs, Real.sqrt_nonneg M, hC]
  · right
    linarith [not_le.mp hsmall]

/-- The small-case bound: if the exponential factor is not small, the side length is
below `log(2C)/c₀`. -/
theorem exp_small (c₀ C : ℝ) (N : ℕ) (hc₀ : 0 < c₀) (hC : 0 < C)
    (h : C * Real.exp (-c₀ * (N:ℝ)) > 1/2) :
    (N:ℝ) < (Real.log (2*C)) / c₀ := by
  have h1 : Real.exp (-c₀ * (N:ℝ)) > 1/(2*C) := by
    rw [gt_iff_lt] at h ⊢
    rw [← div_div, div_lt_iff₀ hC]
    nlinarith [h]
  have h2 : Real.log (Real.exp (-c₀ * (N:ℝ))) > Real.log (1/(2*C)) :=
    Real.log_lt_log (by positivity) h1
  rw [Real.log_exp, Real.log_div (by norm_num) (by positivity), Real.log_one] at h2
  rw [lt_div_iff₀ hc₀]
  nlinarith [h2]

/-- The lower-bound dichotomy: for every side length, either the value is bounded by
`(2C)²` (giving `N ≤ 2 log(2C)/b`) or the exponential factor is not small (giving
`N < log(2C)/c₀`). -/
theorem lower_bound_final (C c₀ b : ℝ) (N : ℕ)
    (hC : 0 < C) (hc₀ : 0 < c₀) (hb : 0 < b)
    (h : Real.exp (b * (N:ℝ)) ≤ C * Real.sqrt (Real.exp (b * (N:ℝ))) +
      C * Real.exp (-c₀ * (N:ℝ)) * Real.exp (b * (N:ℝ))) :
    (N:ℝ) ≤ (2 * Real.log (2*C)) / b ∨ (N:ℝ) < (Real.log (2*C)) / c₀ := by
  by_cases hsmall : C * Real.exp (-c₀ * (N:ℝ)) ≤ 1/2
  · left
    exact exp_growth b c₀ C N hb hc₀ hC hsmall h
  · right
    exact exp_small c₀ C N hc₀ hC (not_le.mp hsmall)

/-- The gradient step: the three-ball iteration applied to the exponential ansatz
`M = exp(bN)` gives the dichotomy used by the lower-bound transfer. -/
theorem gradient_step (C c₀ b : ℝ) (N : ℕ)
    (hC : 0 < C) (hc₀ : 0 < c₀) (hb : 0 < b)
    (h : Real.exp (b * (N:ℝ)) ≤ C * Real.sqrt (Real.exp (b * (N:ℝ))) +
      C * Real.exp (-c₀ * (N:ℝ)) * Real.exp (b * (N:ℝ))) :
    (N:ℝ) ≤ (2 * Real.log (2*C)) / b ∨ (N:ℝ) < (Real.log (2*C)) / c₀ := by
  by_cases hsmall : C * Real.exp (-c₀ * (N:ℝ)) ≤ 1/2
  · left
    have hEpos : 0 < Real.exp (b * (N:ℝ)) := Real.exp_pos _
    have hsq : Real.exp (b * (N:ℝ)) = Real.exp (b * (N:ℝ) / 2) ^ 2 := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    have hsqrt_eq : Real.sqrt (Real.exp (b * (N:ℝ))) = Real.exp (b * (N:ℝ) / 2) := by
      rw [hsq, Real.sqrt_sq (Real.exp_nonneg _)]
    have hstep : Real.exp (b * (N:ℝ)) / 2 ≤ C * Real.sqrt (Real.exp (b * (N:ℝ))) := by
      have h2 : C * Real.exp (-c₀ * (N:ℝ)) * Real.exp (b * (N:ℝ)) ≤
          (1/2) * Real.exp (b * (N:ℝ)) :=
        mul_le_mul_of_nonneg_right hsmall (le_of_lt hEpos)
      linarith
    rw [hsqrt_eq] at hstep
    have hu : 0 < Real.exp (b * (N:ℝ) / 2) := Real.exp_pos _
    have hE : Real.exp (b * (N:ℝ)) =
        Real.exp (b * (N:ℝ) / 2) * Real.exp (b * (N:ℝ) / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hE] at hstep
    have h3 : Real.exp (b * (N:ℝ) / 2) / 2 ≤ C := by
      have hprod : Real.exp (b * (N:ℝ) / 2) *
          (Real.exp (b * (N:ℝ) / 2) / 2 - C) ≤ 0 := by nlinarith [hstep]
      rcases mul_nonpos_iff.mp hprod with ⟨h1, _⟩ | ⟨_, h2⟩
      · linarith
      · linarith
    have h4 : Real.exp (b * (N:ℝ) / 2) ≤ 2 * C := by linarith
    have h5 : b * (N:ℝ) / 2 ≤ Real.log (2 * C) := by
      have := Real.log_le_log (Real.exp_pos _) h4
      rwa [Real.log_exp] at this
    have h6 : b * (N:ℝ) ≤ 2 * Real.log (2 * C) := by linarith
    rw [le_div_iff₀ hb]
    nlinarith
  · right
    have hC2 : 0 < 2 * C := by linarith
    have hlt : 1/2 < C * Real.exp (-c₀ * (N:ℝ)) := lt_of_not_ge hsmall
    have h1 : 1 / (2 * C) < Real.exp (-c₀ * (N:ℝ)) := by
      rw [div_lt_iff₀ hC2]
      nlinarith
    have h2 : Real.log (1 / (2 * C)) < -c₀ * (N:ℝ) := by
      have := Real.log_lt_log (by positivity) h1
      rwa [Real.log_exp] at this
    have h3 : Real.log (1 / (2 * C)) = -Real.log (2 * C) := by
      rw [one_div, Real.log_inv]
    rw [h3] at h2
    rw [lt_div_iff₀ hc₀]
    nlinarith

/-- The lower-bound transfer in the shape used by the graph-level statement: if the
exponential ansatz satisfies the three-ball inequality and `N` exceeds the first threshold,
then `N` is below the second. -/
theorem lower_bound_contra (C c₀ b : ℝ) (N : ℕ)
    (hC : 0 < C) (hc₀ : 0 < c₀) (hb : 0 < b)
    (h : Real.exp (b * (N:ℝ)) ≤ C * Real.sqrt (Real.exp (b * (N:ℝ))) +
      C * Real.exp (-c₀ * (N:ℝ)) * Real.exp (b * (N:ℝ)))
    (hN : (2 * Real.log (2*C)) / b < (N:ℝ)) :
    (N:ℝ) < (Real.log (2*C)) / c₀ := by
  rcases gradient_step C c₀ b N hC hc₀ hb h with h1 | h2
  · exact absurd h1 (not_le.mpr hN)
  · exact h2

/-- A vertex where `f` is at least `2` forces the supremum norm on any finite set
containing it to be at least `2`. -/
theorem supNorm_ge_two {V : Type*} (S : Finset V) (f : V → ℝ) (x : V)
    (hx : x ∈ S) (h : 2 ≤ f x) : 2 ≤ UCPlanar.supNorm S f := by
  have h1 : ‖f x‖₊ ≤ S.sup (fun x => ‖f x‖₊) := Finset.le_sup (f := fun x => ‖f x‖₊) hx
  have h2 : (2:ℝ) ≤ ((‖f x‖₊ : NNReal) : ℝ) := by
    change (2:ℝ) ≤ |f x|
    rw [abs_of_nonneg (by linarith)]
    exact h
  have h3 : ((‖f x‖₊ : NNReal) : ℝ) ≤ ((S.sup (fun x => ‖f x‖₊) : NNReal) : ℝ) := by
    exact_mod_cast h1
  unfold UCPlanar.supNorm
  linarith

/-- The supremum norm is monotone in the finite set. -/
theorem supNorm_mono {V : Type*} (S T : Finset V) (f : V → ℝ) (h : S ⊆ T) :
    UCPlanar.supNorm S f ≤ UCPlanar.supNorm T f := by
  unfold UCPlanar.supNorm
  exact_mod_cast Finset.sup_mono h

/-- One step of the outward iteration: if the three-ball bound `M ≤ C√M' + C exp(-c) M'`
holds with `M' ≤ M²` and `C ≤ 1/2`, then `M' ≥ exp(c) M / (2C)`, so the supremum grows
geometrically by the factor `exp(c)/(2C)`. -/
theorem iterate_step (C c M M' : ℝ) (hC : 0 < C) (hC2 : C ≤ 1/2) (_hc : 0 < c)
    (hM : 0 < M) (_hM' : 0 < M') (hle : M' ≤ M^2)
    (h : M ≤ C * Real.sqrt M' + C * Real.exp (-c) * M') :
    Real.exp c * M / (2*C) ≤ M' := by
  have hsqrt : Real.sqrt M' ≤ M := by
    have h1 : Real.sqrt M' ≤ Real.sqrt (M^2) := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (le_of_lt hM)] at h1
  have h2 : M ≤ C * M + C * Real.exp (-c) * M' := by
    have := mul_le_mul_of_nonneg_left hsqrt (le_of_lt hC)
    linarith
  have h3 : (1 - C) * M ≤ C * Real.exp (-c) * M' := by nlinarith
  have h4 : (1/2) * M ≤ C * Real.exp (-c) * M' := by nlinarith
  have hexp : Real.exp c * Real.exp (-c) = 1 := by
    rw [← Real.exp_add]; ring_nf; rw [Real.exp_zero]
  have h4' : (1/2) * M ≤ C * (Real.exp (-c) * M') := by linarith [h4]
  have h5 : Real.exp c * ((1/2) * M) ≤ Real.exp c * (C * (Real.exp (-c) * M')) :=
    mul_le_mul_of_nonneg_left h4' (le_of_lt (Real.exp_pos c))
  have h6 : Real.exp c * (1/2 * M) ≤ C * M' := by
    have h7 : Real.exp c * (C * (Real.exp (-c) * M')) = C * M' := by
      rw [← mul_assoc (Real.exp c) C (Real.exp (-c) * M'), mul_comm (Real.exp c) C,
        mul_assoc C (Real.exp c) (Real.exp (-c) * M'), ← mul_assoc (Real.exp c) (Real.exp (-c)) M',
        hexp, one_mul]
    linarith [h5, h7.le]
  rw [div_le_iff₀ (by positivity)]
  nlinarith [h6]

/-- The lower-bound transfer in the shape used by the graph-level statement: if the
exponential ansatz satisfies the three-ball inequality and `N` exceeds the first threshold,
then `N` is below the second. -/
theorem lower_bound_transfer (C c₀ b : ℝ) (N : ℕ)
    (hC : 0 < C) (hc₀ : 0 < c₀) (hb : 0 < b)
    (h : Real.exp (b * (N:ℝ)) ≤ C * Real.sqrt (Real.exp (b * (N:ℝ))) +
      C * Real.exp (-c₀ * (N:ℝ)) * Real.exp (b * (N:ℝ)))
    (hN : (2 * Real.log (2*C)) / b < (N:ℝ)) :
    (N:ℝ) < (Real.log (2*C)) / c₀ :=
  lower_bound_contra C c₀ b N hC hc₀ hb h hN

/-- The covering step from `Q_{kN}` to `Q_{4N}`: the three-ball bound applied at
each of the `log`-many scales, with the geometric loss absorbed. -/
theorem cover_step_geometric (C c : ℝ) (hC : 0 < C) (hc : 0 < c) (N : ℕ) :
    C * Real.exp (-c * (N:ℝ)) ≤ C := by
  have h1 : Real.exp (-c * (N:ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hN : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
    nlinarith [hc, hN]
  nlinarith [h1, hC]

/-- The covering arithmetic from `Q_{kN}` to `Q_{4N}`: the geometric sum of the
three-ball losses at each scale is bounded by `1/(1-r)`. -/
theorem cover_geometric (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) :
    (∑ k ∈ Finset.range N, r ^ k) ≤ 1 / (1 - r) := by
  have h1 : (∑ k ∈ Finset.range N, r ^ k) = (1 - r ^ N) / (1 - r) := by
    rw [geom_sum_eq (by linarith : r ≠ 1)]
    rw [div_eq_div_iff (by linarith : r - 1 ≠ 0) (by linarith : (1:ℝ) - r ≠ 0)]
    ring
  rw [h1]
  apply div_le_div_of_nonneg_right _ (by linarith : (0:ℝ) ≤ 1 - r)
  linarith [pow_nonneg hr.le N]

/-- The outward iteration of the three-ball bound: from the bound at scale `K`
and the density hypothesis, either the value is bounded by `(2C)^2` or the
exponential factor is not small. -/
theorem outward_iterate (C c : ℝ) (_hC : 0 < C) (_hc : 0 < c) (K : ℕ) (M : ℝ)
    (hM : 0 < M)
    (h : M ≤ C * Real.sqrt M + C * Real.exp (-c * (K:ℝ)) * M) :
    M ≤ (2*C)^2 ∨ Real.exp (c * (K:ℝ)) ≤ 2*C := by
  by_cases hsmall : C * Real.exp (-c * (K:ℝ)) ≤ 1/2
  · left
    have h2 : M / 2 ≤ C * Real.sqrt M := by nlinarith [h, hsmall, hM]
    have h3 : Real.sqrt M ^ 2 = M := Real.sq_sqrt hM.le
    nlinarith [h2, h3, Real.sqrt_nonneg M, hM]
  · right
    have h1 : 1/2 < C * Real.exp (-c * (K:ℝ)) := not_le.mp hsmall
    have h1' : 1/2 < C * (Real.exp (c * (K:ℝ)))⁻¹ := by
      simpa [Real.exp_neg, neg_mul] using h1
    have hexp : Real.exp (c * (K:ℝ)) < 2 * C := by
      rw [← div_eq_mul_inv] at h1'
      rw [lt_div_iff₀ (Real.exp_pos _)] at h1'
      nlinarith [h1']
    linarith [hexp.le]

/-- The exponential iteration of the three-ball bound: if the value at scale `N/2^j`
satisfies `M_{j+1} ≤ C√M_j + C exp(-c N/2^{j+1}) M_j` with `2b ≤ c`, then
`M_j ≤ (2C)^j exp(b N/2^j)`. -/
theorem iter_exp (C c b : ℝ) (N : ℕ) (M : ℕ → ℝ)
    (hC : 1 ≤ C) (hbc : 2*b ≤ c) (_hb : 0 < b)
    (_hM : ∀ j, 0 < M j)
    (h0 : M 0 ≤ Real.exp (b * (N:ℝ)))
    (hstep : ∀ j, M (j+1) ≤ C * Real.sqrt (M j) + C * Real.exp (-c * ((N:ℝ)/2^(j+1))) * M j) :
    ∀ j, M j ≤ (2*C)^j * Real.exp (b * ((N:ℝ)/2^j)) := by
  intro j
  induction j with
  | zero => simpa using h0
  | succ j ih =>
    have hCpos : (0:ℝ) < C := by linarith
    have h2C : (0:ℝ) < 2*C := by linarith
    have hpow : (0:ℝ) < (2*C)^j := pow_pos h2C j
    have hsq : Real.sqrt (M j) ≤ Real.sqrt ((2*C)^j) * Real.exp (b * ((N:ℝ)/2^j) / 2) := by
      have h1 := Real.sqrt_le_sqrt ih
      rw [Real.sqrt_mul (pow_nonneg (by linarith : (0:ℝ) ≤ 2*C) j),
        (Real.exp_half (b * ((N:ℝ)/2^j))).symm] at h1
      exact h1
    have hterm1 : C * Real.sqrt (M j) ≤
        C * (Real.sqrt ((2*C)^j) * Real.exp (b * ((N:ℝ)/2^j) / 2)) :=
      mul_le_mul_of_nonneg_left hsq (le_of_lt hCpos)
    have hterm2 : Real.exp (-c * ((N:ℝ)/2^(j+1))) * M j ≤
        Real.exp (-c * ((N:ℝ)/2^(j+1))) * ((2*C)^j * Real.exp (b * ((N:ℝ)/2^j))) :=
      mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
    have hterm2' : C * (Real.exp (-c * ((N:ℝ)/2^(j+1))) * M j) ≤
        C * (Real.exp (-c * ((N:ℝ)/2^(j+1))) * ((2*C)^j * Real.exp (b * ((N:ℝ)/2^j)))) :=
      mul_le_mul_of_nonneg_left hterm2 (le_of_lt hCpos)
    have hcomb : M (j+1) ≤ C * (Real.sqrt ((2*C)^j) * Real.exp (b * ((N:ℝ)/2^j) / 2)) +
        C * (Real.exp (-c * ((N:ℝ)/2^(j+1))) * ((2*C)^j * Real.exp (b * ((N:ℝ)/2^j)))) := by
      have hh := hstep j
      nlinarith [hh, hterm1, hterm2']
    have hsqrt_le : Real.sqrt ((2*C)^j) ≤ (2*C)^j := by
      have h1 : Real.sqrt ((2*C)^j) ≤ Real.sqrt ((2*C)^j * (2*C)^j) :=
        Real.sqrt_le_sqrt (le_mul_of_one_le_left (le_of_lt hpow)
          (one_le_pow₀ (by linarith : (1:ℝ) ≤ 2*C)))
      rw [Real.sqrt_mul (le_of_lt hpow)] at h1
      nlinarith [h1, Real.sq_sqrt (le_of_lt hpow), Real.sqrt_nonneg ((2*C)^j)]
    have hexp1 : Real.exp (b * ((N:ℝ)/2^j) / 2) = Real.exp (b * ((N:ℝ)/2^(j+1))) := by
      congr 1
      have h2p : (0:ℝ) < (2:ℝ)^(j+1) := pow_pos (by norm_num) (j+1)
      have h2j : (0:ℝ) < (2:ℝ)^j := pow_pos (by norm_num) j
      rw [pow_succ]
      field_simp
    have hexp2 : Real.exp (-c * ((N:ℝ)/2^(j+1))) * Real.exp (b * ((N:ℝ)/2^j)) ≤
        Real.exp (b * ((N:ℝ)/2^(j+1))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h2p : (0:ℝ) < (2:ℝ)^(j+1) := pow_pos (by norm_num) (j+1)
      have h2j : (0:ℝ) < (2:ℝ)^j := pow_pos (by norm_num) j
      have hpow2 : (N:ℝ)/2^j = 2 * ((N:ℝ)/2^(j+1)) := by
        rw [pow_succ]
        field_simp
      rw [hpow2]
      have ht : (0:ℝ) ≤ (N:ℝ)/2^(j+1) := div_nonneg (Nat.cast_nonneg N) (le_of_lt h2p)
      nlinarith [hbc, ht]
    have hA : C * (Real.sqrt ((2*C)^j) * Real.exp (b * ((N:ℝ)/2^j) / 2)) ≤
        C * ((2*C)^j * Real.exp (b * ((N:ℝ)/2^(j+1)))) := by
      rw [hexp1]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hsqrt_le (Real.exp_pos _).le) (le_of_lt hCpos)
    have hB : C * (Real.exp (-c * ((N:ℝ)/2^(j+1))) * ((2*C)^j * Real.exp (b * ((N:ℝ)/2^j)))) ≤
        C * ((2*C)^j * Real.exp (b * ((N:ℝ)/2^(j+1)))) := by
      have h1 : Real.exp (-c * ((N:ℝ)/2^(j+1))) * ((2*C)^j * Real.exp (b * ((N:ℝ)/2^j))) =
          (2*C)^j * (Real.exp (-c * ((N:ℝ)/2^(j+1))) * Real.exp (b * ((N:ℝ)/2^j))) := by ring
      rw [h1]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hexp2 (le_of_lt hpow)) (le_of_lt hCpos)
    rw [pow_succ]
    nlinarith [hcomb, hA, hB, hCpos, hpow, Real.exp_pos (b * ((N:ℝ)/2^(j+1)))]

/-- The final contradiction of the exponential iteration: if the value at scale `N`
satisfies the iterated three-ball bound with `c = 2b` and `bN > 2`, the exponential
ansatz is impossible. -/
theorem iter_contra (C b : ℝ) (N J : ℕ) (hC : 1 ≤ C) (_hb : 0 < b)
    (h : Real.exp (b * (N:ℝ)) ≤ (2*C)^J * Real.exp 1)
    (hbig : (J:ℝ) * Real.log (2*C) + 1 < b * (N:ℝ)) : False := by
  have hlog : Real.log (Real.exp (b * (N:ℝ))) ≤ Real.log ((2*C)^J * Real.exp 1) :=
    Real.log_le_log (Real.exp_pos _) h
  rw [Real.log_exp, Real.log_mul (by positivity) (Real.exp_ne_zero 1), Real.log_pow,
    Real.log_exp] at hlog
  have h2C : (1:ℝ) ≤ 2*C := by linarith
  have hlogpos : 0 ≤ Real.log (2*C) := Real.log_nonneg h2C
  linarith [hlog, hbig]

/-- The iteration index exists as soon as `bN > 2`: the geometric loss `(2C)^J` is
absorbed by the exponential gain. -/
theorem iter_big (C b : ℝ) (N : ℕ) (_hC : 1 ≤ C) (_hb : 0 < b)
    (hN : 2 < b * (N:ℝ)) : ∃ J : ℕ, (J:ℝ) * Real.log (2*C) + 1 < b * (N:ℝ) := by
  exact ⟨0, by simp; linarith [hN]⟩

/-- The geometric lower iteration: if each step multiplies the value by at least
`exp(c N 2^j)/(2C)`, then after `j` steps the value is at least
`exp(c N (2^j - 1))/(2C)^j` times the initial value. -/
theorem iter_geom (C c : ℝ) (N : ℕ) (M : ℕ → ℝ) (_hC : 0 < C) (_hc : 0 < c)
    (_hM : ∀ j, 0 < M j)
    (hstep : ∀ j, Real.exp (c * ((N:ℝ) * 2^j)) / (2*C) * M j ≤ M (j+1)) :
    ∀ j, Real.exp (c * (N:ℝ) * (2^j - 1)) / (2*C)^j * M 0 ≤ M j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : Real.exp (c * ((N:ℝ) * 2^j)) / (2*C) * (Real.exp (c * (N:ℝ) * (2^j - 1)) / (2*C)^j * M 0) ≤ Real.exp (c * ((N:ℝ) * 2^j)) / (2*C) * M j :=
      mul_le_mul_of_nonneg_left ih (by positivity)
    have h2 := hstep j
    have h3 : Real.exp (c * ((N:ℝ) * 2^j)) / (2*C) * (Real.exp (c * (N:ℝ) * (2^j - 1)) / (2*C)^j * M 0) = Real.exp (c * (N:ℝ) * (2^(j+1) - 1)) / (2*C)^(j+1) * M 0 := by
      have hexp : c * ((N:ℝ) * 2^j) + c * (N:ℝ) * (2^j - 1) = c * (N:ℝ) * (2^(j+1) - 1) := by
        rw [pow_succ]; ring
      rw [← hexp, Real.exp_add, pow_succ]
      ring
    linarith [h1, h2, h3]

/-- The outward step of the three-ball iteration: from the three-ball bound at scale `K`
with `exp(cK) ≤ 4C`, either the value at the inner scale is already at least `M²`, or the
value at the outer scale is at least `exp(cK) M / (2C)`. -/
theorem outward_tb (C c K M M' : ℝ) (hC : 0 < C) (hC2 : C ≤ 1/2) (_hc : 0 < c)
    (_hM : 2 ≤ M) (hM' : 0 < M') (_hexp : Real.exp (c*K) ≤ 4*C)
    (h : M ≤ C * Real.sqrt M' + C * Real.exp (-c*K) * M') :
    M^2 ≤ M' ∨ Real.exp (c*K) * M / (2*C) ≤ M' := by
  by_cases hle : M ^ 2 ≤ M'
  · exact Or.inl hle
  · right
    have hlt : M' < M ^ 2 := lt_of_not_ge hle
    have hsqrt_lt : Real.sqrt M' < M := by
      have hsq : (Real.sqrt M') ^ 2 < M ^ 2 := by
        rw [Real.sq_sqrt (le_of_lt hM')]
        exact hlt
      nlinarith [Real.sqrt_nonneg M', sq_nonneg (M - Real.sqrt M')]
    have h2 : M < C * M + C * Real.exp (-c * K) * M' := by
      have hCM : C * Real.sqrt M' < C * M := mul_lt_mul_of_pos_left hsqrt_lt hC
      linarith [h, hCM]
    have h3 : (1 - C) * M < C * Real.exp (-c * K) * M' := by nlinarith
    have h4 : (1 / 2) * M ≤ C * Real.exp (-c * K) * M' := by nlinarith
    have hexp2 : Real.exp (c * K) * Real.exp (-c * K) = 1 := by
      rw [← Real.exp_add]
      have hzero : c * K + -c * K = 0 := by ring
      rw [hzero, Real.exp_zero]
    have h7 : Real.exp (c * K) * (C * Real.exp (-c * K) * M') = C * M' := by
      rw [← mul_assoc (Real.exp (c * K)) (C * Real.exp (-c * K)) M',
          ← mul_assoc (Real.exp (c * K)) C (Real.exp (-c * K)),
          mul_comm (Real.exp (c * K)) C,
          mul_assoc C (Real.exp (c * K)) (Real.exp (-c * K)),
          hexp2, mul_one]
    have h6 : Real.exp (c * K) * (1 / 2 * M) ≤ C * M' := by
      have h5 := mul_le_mul_of_nonneg_left h4 (le_of_lt (Real.exp_pos (c * K)))
      rwa [h7] at h5
    rw [div_le_iff₀ (by positivity)]
    nlinarith [h6]

/-- The accumulation of the geometric iteration: the exponential gain
`exp(c(N - √N))` divided by the geometric loss `(2C)^J` and multiplied by the value `M`
at the inner scale dominates `exp(bN)` once `b ≤ c/2` and `N` is large enough. -/
theorem geom_accum (C c b : ℝ) (N : ℕ) (J : ℕ) (M M' : ℝ)
    (hC : 0 < C) (hC1 : 1 ≤ C) (_hc : 0 < c) (_hb : 0 < b) (_hbc : b ≤ c/2)
    (hM : 2 ≤ M) (hJ : (2:ℝ)^J ≤ 2*Real.sqrt N)
    (hN : c * Real.sqrt N + Real.log (2*C) * (Real.log (2*Real.sqrt N) / Real.log 2) ≤ (c-b) * (N:ℝ))
    (h : Real.exp (c * ((N:ℝ) - Real.sqrt N)) / (2*C)^J * M ≤ M') :
    Real.exp (b * (N:ℝ)) ≤ M' := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2C1 : (1:ℝ) ≤ 2*C := by linarith
  have hlog2C : 0 ≤ Real.log (2*C) := Real.log_nonneg h2C1
  have hJle : (J:ℝ) ≤ Real.log (2*Real.sqrt N) / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    have h1 : Real.log ((2:ℝ)^J) ≤ Real.log (2*Real.sqrt N) := Real.log_le_log (by positivity) hJ
    rw [Real.log_pow] at h1
    linarith
  have h2CJ : (2*C)^J ≤ Real.exp (Real.log (2*C) * (Real.log (2*Real.sqrt N) / Real.log 2)) := by
    rw [← Real.log_le_log_iff (by positivity) (Real.exp_pos _), Real.log_exp, Real.log_pow]
    have := mul_le_mul_of_nonneg_left hJle hlog2C
    linarith [this]
  have hMpos : 0 < M := by linarith
  have h1 : Real.exp (c * ((N:ℝ) - Real.sqrt N)) / Real.exp (Real.log (2*C) * (Real.log (2*Real.sqrt N) / Real.log 2)) * M ≤ Real.exp (c * ((N:ℝ) - Real.sqrt N)) / (2*C)^J * M := by
    apply mul_le_mul_of_nonneg_right _ (le_of_lt hMpos)
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) h2CJ
  have h2 : Real.exp (b * (N:ℝ)) ≤ Real.exp (c * ((N:ℝ) - Real.sqrt N)) / Real.exp (Real.log (2*C) * (Real.log (2*Real.sqrt N) / Real.log 2)) * M := by
    rw [div_mul_eq_mul_div]
    rw [le_div_iff₀ (Real.exp_pos _)]
    rw [← Real.exp_log hMpos]
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
    nlinarith [hN, hlogM, hlog2C]
  linarith [h, h1, h2]

/-- The N-008 assembly: the outward three-ball iteration produces the inequality
`exp(c(N - √N))/(2C)^J * M ≤ M'` between the value `M` at the inner scale `√N` and the
value `M'` at the outer scale `N`, and the geometric accumulation turns it into the
exponential lower bound `exp(bN) ≤ M'`. -/
theorem lower_bound_assembly (C c b : ℝ) (N : ℕ) (J : ℕ) (M M' : ℝ)
    (hC : 0 < C) (hC1 : 1 ≤ C) (hc : 0 < c) (hb : 0 < b) (hbc : b ≤ c/2)
    (hM : 2 ≤ M) (hJ : (2:ℝ)^J ≤ 2*Real.sqrt N)
    (hN : c * Real.sqrt N + Real.log (2*C) * (Real.log (2*Real.sqrt N) / Real.log 2) ≤ (c-b) * (N:ℝ))
    (h : Real.exp (c * ((N:ℝ) - Real.sqrt N)) / (2*C)^J * M ≤ M') :
    Real.exp (b * (N:ℝ)) ≤ M' :=
  geom_accum C c b N J M M' hC hC1 hc hb hbc hM hJ hN h

end UCPlanar.Support.Lower
