/-
Assembly of the polynomial approximation: the Newton interpolation of the orbit data at a corner
of the square, the sharp discrete Taylor remainder, the derivative bound, and the change of
variables to the drawing.
-/
import UCPlanar.Support.Poly.Change

open scoped BigOperators Classical
set_option autoImplicit false

set_option maxHeartbeats 1000000

namespace UCPlanar.Support

/-- The lattice vector with coordinates `(a, b)` has those coordinates. -/
theorem orbitVec_apply (a b : ℕ) (j : Fin 2) :
    (((((a : ℤ) • UCPlanar.Support.e₁ + (b : ℤ) • UCPlanar.Support.e₂) j : ℤ) : ℝ))
      = if j = 0 then (a : ℝ) else (b : ℝ) := by
  fin_cases j <;> simp [UCPlanar.Support.e₁, UCPlanar.Support.e₂]

theorem orbitVec_norm_le (a b : ℕ) (M : ℝ) (ha : (a : ℝ) ≤ M) (hb : (b : ℝ) ≤ M) :
    ‖(fun j => (((((a : ℤ) • UCPlanar.Support.e₁ + (b : ℤ) • UCPlanar.Support.e₂) j : ℤ) : ℝ))
        : UCPlanar.Plane)‖ ≤ M := by
  have hM0 : (0:ℝ) ≤ M := le_trans (Nat.cast_nonneg a) ha
  refine (pi_norm_le_iff_of_nonneg hM0).mpr ?_
  intro j
  rw [Real.norm_eq_abs, orbitVec_apply]
  by_cases hj : j = 0
  · rw [if_pos hj, abs_of_nonneg (Nat.cast_nonneg a)]
    exact ha
  · rw [if_neg hj, abs_of_nonneg (Nat.cast_nonneg b)]
    exact hb

/-- **The polynomial approximation lemma for `α ≤ 2`**, `ucplanar.tex:438-445`. -/
theorem polynomialApproximation_aux {V : Type*}
    (P : UCPlanar.PeriodicGraph V) (c : V → V → ℝ)
    (hc : LatticeProb.Network.IsCond P.graph c) (hp : P.PeriodicConductance c)
    (hMos : UCPlanar.External.MoserEstimate P c)
    (α : ℝ) (hα : 0 < α) (hα2 : α ≤ 2) :
    ∃ δ R₀ : ℝ, 0 < δ ∧ 0 < R₀ ∧
      ∀ R : ℝ, R₀ ≤ R → ∀ m : ℕ, (m : ℝ) ≤ δ*R →
      ∀ (v : V) (f : V → ℝ),
        LatticeProb.Network.HarmonicOn P.graph c f (P.square (3*R) : Set V) →
        P.PolynomialApproximation R m v f α δ := by
  classical
  obtain ⟨C₁, hC₁0, hC₁⟩ := UCPlanar.Support.exists_mixedDiff_bound P c hc hp hMos
  obtain ⟨K, hK0, hK⟩ := UCPlanar.Support.exists_lattice_count P.period
  obtain ⟨B, hB0, hB⟩ := UCPlanar.Support.exists_period_bound P
  refine ⟨min (min (1/(2*C₁)) (1/(2*(1+8*B*K)))) (α/(96*(K+1)*C₁)),
    max (max 1 (2*C₁)) (max (8*B) (48*C₁/α)), ?_, ?_, ?_⟩
  · refine lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  · exact lt_of_lt_of_le zero_lt_one (le_trans (le_max_left 1 (2*C₁)) (le_max_left _ _))
  set δ : ℝ := min (min (1/(2*C₁)) (1/(2*(1+8*B*K)))) (α/(96*(K+1)*C₁)) with hδdef
  intro R hR m hm v f hf
  have hδ0 : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have hδ1 : δ ≤ 1/(2*C₁) := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ2 : δ ≤ 1/(2*(1+8*B*K)) := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ3 : δ ≤ α/(96*(K+1)*C₁) := min_le_right _ _
  have hR1 : (1:ℝ) ≤ R := le_trans (le_trans (le_max_left 1 (2*C₁)) (le_max_left _ _)) hR
  have hR2C : 2*C₁ ≤ R := le_trans (le_trans (le_max_right 1 (2*C₁)) (le_max_left _ _)) hR
  have hR8B : 8*B ≤ R := le_trans (le_trans (le_max_left (8*B) (48*C₁/α)) (le_max_right _ _)) hR
  have hR48 : 48*C₁/α ≤ R :=
    le_trans (le_trans (le_max_right (8*B) (48*C₁/α)) (le_max_right _ _)) hR
  have hR0 : (0:ℝ) < R := by linarith
  have hfin : ∀ x ∈ P.square (3*R), LatticeProb.Network.netLaplacian P.graph c f x = 0 := by
    intro x hx
    exact hf x (Finset.mem_coe.mpr hx)
  have hmC₁ : ((m:ℝ) + 1) * C₁ ≤ R := by
    have h1 : δ * C₁ ≤ 1/2 := by
      have h := mul_le_mul_of_nonneg_right hδ1 (le_of_lt hC₁0)
      rw [div_mul_eq_mul_div, one_mul] at h
      have h2 : C₁ / (2*C₁) = 1/2 := by field_simp
      linarith [h, h2.le, h2.ge]
    nlinarith [hm, hC₁0, hR0, h1]
  obtain ⟨v', N, hN, hov', hrb⟩ :=
    UCPlanar.Support.exists_rebase P K hK0 hK v (δ*R) (by positivity)
  refine ⟨UCPlanar.Support.changeVar P v' (UCPlanar.Support.orbitPoly P f v' m),
    le_trans (UCPlanar.Support.changeVar_totalDegree_le P v' _)
      (UCPlanar.Support.orbitPoly_totalDegree_le P f v' m), ?_⟩
  intro x hx hox
  obtain ⟨a, b, ha, hb, hab⟩ := hrb x hx hox
  have hN0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hNle : (N:ℝ) ≤ 2*K*(δ*R) + 1 := hN
  have haR : (a:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast ha
  have hbR : (b:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast hb
  have hxnorm : ‖P.pos x‖ ≤ δ*R := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr ?_
    intro i
    simpa [Real.norm_eq_abs] using (UCPlanar.Support.mem_square_iff P (δ*R) x).mp hx i
  have hposv' : ‖P.pos v'‖ ≤ δ*R + B*(2*(N:ℝ)) := by
    have hpos := P.pos_shift ((a : ℤ) • UCPlanar.Support.e₁ + (b : ℤ) • UCPlanar.Support.e₂) v'
    rw [hab] at hpos
    have hsplit : P.pos v' = P.pos x
        - P.period (fun j => (((((a : ℤ) • UCPlanar.Support.e₁
            + (b : ℤ) • UCPlanar.Support.e₂) j : ℤ) : ℝ))) := by
      rw [hpos]; abel
    rw [hsplit]
    have h1 := norm_sub_le (P.pos x)
      (P.period (fun j => (((((a : ℤ) • UCPlanar.Support.e₁
        + (b : ℤ) • UCPlanar.Support.e₂) j : ℤ) : ℝ))))
    have h2 := hB (fun j => (((((a : ℤ) • UCPlanar.Support.e₁
      + (b : ℤ) • UCPlanar.Support.e₂) j : ℤ) : ℝ)))
    have h3 := orbitVec_norm_le a b (2*(N:ℝ)) haR hbR
    have h4 : B * ‖(fun j => (((((a : ℤ) • UCPlanar.Support.e₁
        + (b : ℤ) • UCPlanar.Support.e₂) j : ℤ) : ℝ)) : UCPlanar.Plane)‖ ≤ B * (2*(N:ℝ)) :=
      mul_le_mul_of_nonneg_left h3 hB0
    linarith
  have hrect : ∀ t y : ℕ, t ≤ 2*N → y ≤ 2*N →
      P.shift ((t : ℤ) • UCPlanar.Support.e₁ + (y : ℤ) • UCPlanar.Support.e₂) v'
        ∈ P.square R := by
    intro t y ht hy
    have htR : (t:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast ht
    have hyR : (y:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast hy
    rw [UCPlanar.Support.mem_square_iff]
    intro i
    have hpos := P.pos_shift ((t : ℤ) • UCPlanar.Support.e₁ + (y : ℤ) • UCPlanar.Support.e₂) v'
    rw [hpos, Pi.add_apply]
    have h1 : |P.pos v' i + P.period (fun j => (((((t : ℤ) • UCPlanar.Support.e₁
          + (y : ℤ) • UCPlanar.Support.e₂) j : ℤ) : ℝ))) i|
        ≤ |P.pos v' i| + |P.period (fun j => (((((t : ℤ) • UCPlanar.Support.e₁
          + (y : ℤ) • UCPlanar.Support.e₂) j : ℤ) : ℝ))) i| := abs_add_le _ _
    have h2 : |P.pos v' i| ≤ ‖P.pos v'‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (P.pos v') i
    have h3 : |P.period (fun j => (((((t : ℤ) • UCPlanar.Support.e₁
          + (y : ℤ) • UCPlanar.Support.e₂) j : ℤ) : ℝ))) i|
        ≤ ‖P.period (fun j => (((((t : ℤ) • UCPlanar.Support.e₁
          + (y : ℤ) • UCPlanar.Support.e₂) j : ℤ) : ℝ)))‖ := by
      simpa [Real.norm_eq_abs] using
        norm_le_pi_norm (P.period (fun j => (((((t : ℤ) • UCPlanar.Support.e₁
          + (y : ℤ) • UCPlanar.Support.e₂) j : ℤ) : ℝ)))) i
    have h4 := hB (fun j => (((((t : ℤ) • UCPlanar.Support.e₁
      + (y : ℤ) • UCPlanar.Support.e₂) j : ℤ) : ℝ)))
    have h5 : B * ‖(fun j => (((((t : ℤ) • UCPlanar.Support.e₁
        + (y : ℤ) • UCPlanar.Support.e₂) j : ℤ) : ℝ)) : UCPlanar.Plane)‖ ≤ B * (2*(N:ℝ)) :=
      mul_le_mul_of_nonneg_left (orbitVec_norm_le t y (2*(N:ℝ)) htR hyR) hB0
    have hδR : δ*(1+8*B*K) ≤ 1/2 := by
      have h := mul_le_mul_of_nonneg_right hδ2 (by positivity : (0:ℝ) ≤ 1+8*B*K)
      have h2' : 1/(2*(1+8*B*K)) * (1+8*B*K) = 1/2 := by
        field_simp
      linarith [h, h2'.le, h2'.ge]
    have hA : 4*B*(N:ℝ) ≤ 8*B*K*(δ*R) + 4*B := by
      have h := mul_le_mul_of_nonneg_left hNle (by positivity : (0:ℝ) ≤ 4*B)
      nlinarith [h]
    have hCC : δ*R*(1+8*B*K) ≤ R/2 := by
      have h := mul_le_mul_of_nonneg_left hδR (le_of_lt hR0)
      nlinarith [h]
    linarith [h1, h2, h3, h4, h5, hposv', hA, hCC, hR8B]
  set s : ℝ := UCPlanar.supNorm (P.square (3*R)) f with hsdef
  have hs0 : (0:ℝ) ≤ s := by
    rw [hsdef, UCPlanar.supNorm]
    exact NNReal.coe_nonneg _
  set M : ℝ := ((C₁ * ((m:ℝ) + 1))/R) ^ (m+1) * s with hMdef
  have hMbase : (0:ℝ) ≤ (C₁ * ((m:ℝ) + 1))/R := by positivity
  have hM0 : (0:ℝ) ≤ M := by
    rw [hMdef]
    exact mul_nonneg (pow_nonneg hMbase _) hs0
  have hMbound : ∀ i j : ℕ, i + j = m + 1 → ∀ t y : ℕ, t + i ≤ a → y + j ≤ b →
      |((fwdDiff ((1, 0) : ℕ × ℕ))^[i] ((fwdDiff ((0, 1) : ℕ × ℕ))^[j]
        (fun ab : ℕ × ℕ => UCPlanar.Support.orbitCoord P f v' ab.1 ab.2))) (t, y)| ≤ M := by
    intro i j hij t y hti hyj
    exact hC₁ R hR1 m hmC₁ f hfin v' i j hij t y (hrect t y (by omega) (by omega))
  have hrem := UCPlanar.Support.orbitPoly_remainder_choose P f v' m a b M hM0 hMbound
  have hfx : f x = UCPlanar.Support.orbitCoord P f v' a b := by rw [← hab]; rfl
  have hpx : MvPolynomial.eval (P.pos x)
        (UCPlanar.Support.changeVar P v' (UCPlanar.Support.orbitPoly P f v' m))
      = MvPolynomial.eval (fun k : Fin 2 => if k = 0 then (a:ℝ) else (b:ℝ))
          (UCPlanar.Support.orbitPoly P f v' m) := by
    rw [← hab]
    exact UCPlanar.Support.changeVar_eval_orbit P v' _ a b
  rw [hfx, hpx]
  refine le_trans hrem ?_
  have hmargin : (a:ℝ) + b ≤ (α/(6*C₁))*R := by
    have h6 : (0:ℝ) < 6*C₁ := by linarith
    rw [show (α/(6*C₁))*R = α*R/(6*C₁) by ring, le_div_iff₀ h6]
    have hδ3' : δ * (96*(K+1)*C₁) ≤ α := by
      have h := mul_le_mul_of_nonneg_right hδ3 (by positivity : (0:ℝ) ≤ 96*(K+1)*C₁)
      have h2' : α/(96*(K+1)*C₁) * (96*(K+1)*C₁) = α := by field_simp
      linarith [h, h2'.le, h2'.ge]
    have hR48' : 48*C₁ ≤ α*R := by
      rw [div_le_iff₀ hα] at hR48
      nlinarith [hR48, hα, hR0]
    nlinarith [haR, hbR, hNle, hδ3', hR48', hK0, hδ0, hR0, hC₁0, hB0]
  have hkey := _root_.choose_mul_pow_le_of_margin a b m α C₁ R hα hα2 hC₁0 hR0 hmargin
  have hMeq : M = ((C₁/R) * ((m:ℝ) + 1)) ^ (m+1) * s := by
    rw [hMdef]
    congr 2
    field_simp
  rw [hMeq, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hkey hs0

end UCPlanar.Support
