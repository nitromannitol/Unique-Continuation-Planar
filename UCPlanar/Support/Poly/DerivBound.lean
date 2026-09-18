/-
The derivative bound of the polynomial approximation lemma: iterating the discrete Caccioppoli
inequality across `Q_{2R} ⊂ … ⊂ Q_{3R}` and applying the discrete Moser estimate once bounds the
word differences of a harmonic function on `Q_R` by `(C k / R) ^ k` times its supremum norm on
`Q_{3R}`, where `k` is the order of the difference.
-/
import UCPlanar.Support.Poly.Word
import UCPlanar.Support.Poly.Volume
import UCPlanar.Support.Poly.CaccioppoliLattice
import UCPlanar.External.MoserEstimate

open scoped BigOperators Classical
set_option autoImplicit false

namespace UCPlanar.Support

/-- **The derivative bound**, `ucplanar.tex:452-457 (eq:derivative-bound)`.  The constant inside
the power grows linearly in the order of the difference, which is what the factorial of the
sharp Taylor remainder pays for. -/
theorem exists_derivative_bound {V : Type*} (P : UCPlanar.PeriodicGraph V) (c : V → V → ℝ)
    (hc : LatticeProb.Network.IsCond P.graph c) (hp : P.PeriodicConductance c)
    (hMos : UCPlanar.External.MoserEstimate P c)
    (a₁ a₂ : LatticeProb.Site 2) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ R : ℝ, 1 ≤ R → ∀ w : List (LatticeProb.Site 2),
      (∀ a ∈ w, a = a₁ ∨ a = a₂) → 0 < w.length → (w.length : ℝ) * C₁ ≤ R →
      ∀ f : V → ℝ,
        (∀ x ∈ P.square (3*R), LatticeProb.Network.netLaplacian P.graph c f x = 0) →
        ∀ x ∈ P.square R,
          |P.diffWord w f x| ≤ ((C₁ * (w.length : ℝ)) / R) ^ w.length
              * UCPlanar.supNorm (P.square (3*R)) f := by
  classical
  obtain ⟨CV, hCV0, hCV⟩ := UCPlanar.Support.exists_square_card_bound P
  obtain ⟨D₁, hD₁0, hD₁⟩ := UCPlanar.Support.exists_lattice_caccioppoli P hc hp a₁
  obtain ⟨D₂, hD₂0, hD₂⟩ := UCPlanar.Support.exists_lattice_caccioppoli P hc hp a₂
  obtain ⟨CM, hCM0, hCM⟩ := hMos
  set C : ℝ := max D₁ D₂ with hCdef
  have hC0 : 0 < C := lt_of_lt_of_le hD₁0 (le_max_left _ _)
  set C₀ : ℝ := ‖P.period (fun j => (a₁ j : ℝ))‖ + ‖P.period (fun j => (a₂ j : ℝ))‖ with hC₀def
  have hC₀0 : 0 ≤ C₀ := by positivity
  set A : ℝ := max 1 (3 * CM * Real.sqrt CV) with hAdef
  have hA1 : (1:ℝ) ≤ A := le_max_left _ _
  set C₁ : ℝ := max (A * C) (max C₀ 1) with hC₁def
  have hC₁0 : 0 < C₁ :=
    lt_of_lt_of_le zero_lt_one (le_trans (le_max_right C₀ 1) (le_max_right (A * C) _))
  refine ⟨C₁, hC₁0, ?_⟩
  intro R hR w hw hlen hsmall f hf x hx
  have hR0 : (0:ℝ) < R := by linarith
  have hn0 : (0:ℝ) < (w.length : ℝ) := by exact_mod_cast hlen
  have hlen1 : 1 ≤ w.length := hlen
  set gap : ℝ := R / (w.length : ℝ) with hgapdef
  have hgap0 : 0 < gap := div_pos hR0 hn0
  have hngap : (w.length : ℝ) * gap = R := by
    rw [hgapdef]; field_simp
  have hC₀C₁ : C₀ ≤ C₁ := le_trans (le_max_left C₀ 1) (le_max_right (A * C) _)
  have hC₁gap : C₁ ≤ gap := by
    rw [hgapdef, le_div_iff₀ hn0]
    linarith [hsmall]
  have hC₀gap : C₀ ≤ gap := le_trans hC₀C₁ hC₁gap
  have hnC₀ : (w.length : ℝ) * C₀ ≤ R := by
    have h : (w.length : ℝ) * C₀ ≤ (w.length : ℝ) * C₁ :=
      mul_le_mul_of_nonneg_left hC₀C₁ (le_of_lt hn0)
    linarith
  have hwC₀ : ∀ a ∈ w, ∀ i, |P.period (fun j => (a j : ℝ)) i| ≤ C₀ := by
    intro a ha i
    have hpi : |P.period (fun j => (a j : ℝ)) i| ≤ ‖P.period (fun j => (a j : ℝ))‖ := by
      simpa [Real.norm_eq_abs] using
        norm_le_pi_norm (P.period (fun j => (a j : ℝ))) i
    rcases hw a ha with rfl | rfl
    · have h2 : (0:ℝ) ≤ ‖P.period (fun j => (a₂ j : ℝ))‖ := norm_nonneg _
      rw [hC₀def]; linarith
    · have h2 : (0:ℝ) ≤ ‖P.period (fun j => (a₁ j : ℝ))‖ := norm_nonneg _
      rw [hC₀def]; linarith
  have hcac : ∀ a ∈ w, ∀ r s : ℝ, 0 < r → r + C ≤ s → ∀ g : V → ℝ,
      (∀ y ∈ P.square s, LatticeProb.Network.netLaplacian P.graph c g y = 0) →
      ∑ y ∈ P.square r, P.diff a g y ^ 2 ≤ (C / (s - r)) ^ 2 * ∑ y ∈ P.square s, g y ^ 2 := by
    intro a ha r s hr hrs g hg
    have hsr : (0:ℝ) < s - r := by linarith
    have hsum : (0:ℝ) ≤ ∑ y ∈ P.square s, g y ^ 2 := Finset.sum_nonneg fun y _ => sq_nonneg _
    rcases hw a ha with rfl | rfl
    · have hDC : D₁ ≤ C := le_max_left _ _
      refine le_trans (hD₁ r s hr (by linarith) g hg) ?_
      have hb : (0:ℝ) ≤ D₁ / (s - r) := by positivity
      have hle : D₁ / (s - r) ≤ C / (s - r) := by gcongr
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb hle 2) hsum
    · have hDC : D₂ ≤ C := le_max_right _ _
      refine le_trans (hD₂ r s hr (by linarith) g hg) ?_
      have hb : (0:ℝ) ≤ D₂ / (s - r) := by positivity
      have hle : D₂ / (s - r) ≤ C / (s - r) := by gcongr
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb hle 2) hsum
  have hharm2 : ∀ y ∈ P.square (2*R),
      LatticeProb.Network.netLaplacian P.graph c (P.diffWord w f) y = 0 := by
    intro y hy
    refine UCPlanar.Support.diffWord_harmonic P c hp C₀ hC₀0 w hwC₀ f (3*R) hf y ?_
    exact UCPlanar.Support.square_mono P (by linarith) hy
  have hscale : 2*R + (w.length : ℝ) * gap = 3*R := by rw [hngap]; ring
  have hl2 : ∑ y ∈ P.square (2*R), P.diffWord w f y ^ 2
      ≤ ((C / gap) ^ w.length) ^ 2 * ∑ y ∈ P.square (3*R), f y ^ 2 := by
    have hCC₁ : C ≤ C₁ :=
      le_trans (le_mul_of_one_le_left hC0.le hA1) (le_max_left (A * C) _)
    have hCgap : C ≤ gap := le_trans hCC₁ hC₁gap
    have h := UCPlanar.Support.diffWord_l2_iterate P c hp C C₀ gap hC0 hC₀0 hgap0 hC₀gap hCgap
      w hwC₀
      hcac f (2*R) (by linarith) (by rw [hscale]; exact hf)
    rwa [hscale] at h
  have hmos := hCM R (2*R) hR0 (by linarith) (P.diffWord w f) hharm2 x hx
  rw [show 2*R - R = R by ring] at hmos
  have hS1nn : (0:ℝ) ≤ ∑ y ∈ P.square (2*R), P.diffWord w f y ^ 2 :=
    Finset.sum_nonneg fun y _ => sq_nonneg _
  have hS2nn : (0:ℝ) ≤ ∑ y ∈ P.square (3*R), f y ^ 2 :=
    Finset.sum_nonneg fun y _ => sq_nonneg _
  have hsnn : (0:ℝ) ≤ UCPlanar.supNorm (P.square (3*R)) f := by
    rw [UCPlanar.supNorm]; exact NNReal.coe_nonneg _
  have hpowgap : (0:ℝ) ≤ (C / gap) ^ w.length := by positivity
  have hsqrt1 : Real.sqrt (∑ y ∈ P.square (2*R), P.diffWord w f y ^ 2)
      ≤ (C / gap) ^ w.length * Real.sqrt (∑ y ∈ P.square (3*R), f y ^ 2) := by
    have h1 := Real.sqrt_le_sqrt hl2
    rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hpowgap] at h1
  have hcard : ((P.square (3*R)).card : ℝ) ≤ CV * (3*R)^2 := hCV (3*R) (by linarith)
  have hsqrt2 : Real.sqrt (∑ y ∈ P.square (3*R), f y ^ 2)
      ≤ Real.sqrt CV * (3*R) * UCPlanar.supNorm (P.square (3*R)) f := by
    have hnn : (0:ℝ) ≤ Real.sqrt CV * (3*R) * UCPlanar.supNorm (P.square (3*R)) f :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by linarith)) hsnn
    have hb : (∑ y ∈ P.square (3*R), f y ^ 2)
        ≤ (Real.sqrt CV * (3*R) * UCPlanar.supNorm (P.square (3*R)) f)^2 := by
      have h1 := UCPlanar.Support.sum_sq_le_card_mul_supNorm_sq (P.square (3*R)) f
      have h2 : ((P.square (3*R)).card : ℝ) * UCPlanar.supNorm (P.square (3*R)) f ^ 2
          ≤ (CV * (3*R)^2) * UCPlanar.supNorm (P.square (3*R)) f ^ 2 :=
        mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      have h3 : (Real.sqrt CV * (3*R) * UCPlanar.supNorm (P.square (3*R)) f)^2
          = CV * (3*R)^2 * UCPlanar.supNorm (P.square (3*R)) f ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (le_of_lt hCV0)]
      rw [h3]
      linarith
    calc Real.sqrt (∑ y ∈ P.square (3*R), f y ^ 2)
        ≤ Real.sqrt ((Real.sqrt CV * (3*R) * UCPlanar.supNorm (P.square (3*R)) f)^2) :=
          Real.sqrt_le_sqrt hb
      _ = Real.sqrt CV * (3*R) * UCPlanar.supNorm (P.square (3*R)) f := Real.sqrt_sq hnn
  have hchain : |P.diffWord w f x|
      ≤ (CM / R) * ((C / gap) ^ w.length *
          (Real.sqrt CV * (3*R) * UCPlanar.supNorm (P.square (3*R)) f)) := by
    refine le_trans hmos ?_
    have hCMR : (0:ℝ) ≤ CM / R := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hCMR
    refine le_trans hsqrt1 ?_
    exact mul_le_mul_of_nonneg_left hsqrt2 hpowgap
  have hgapeq : C / gap = C * (w.length : ℝ) / R := by
    rw [hgapdef]
    field_simp
  have hrewrite : (CM / R) * ((C / gap) ^ w.length *
        (Real.sqrt CV * (3*R) * UCPlanar.supNorm (P.square (3*R)) f))
      = (3 * CM * Real.sqrt CV) * ((C * (w.length : ℝ) / R) ^ w.length
          * UCPlanar.supNorm (P.square (3*R)) f) := by
    rw [hgapeq]
    field_simp
  rw [hrewrite] at hchain
  refine le_trans hchain ?_
  have hpow2 : (0:ℝ) ≤ (C * (w.length : ℝ) / R) ^ w.length := by positivity
  have hAle : 3 * CM * Real.sqrt CV ≤ A := le_max_right _ _
  have hAn : A ≤ A ^ w.length := by
    calc A = A ^ 1 := (pow_one A).symm
      _ ≤ A ^ w.length := pow_le_pow_right₀ hA1 hlen1
  have hstep1 : (3 * CM * Real.sqrt CV) * ((C * (w.length : ℝ) / R) ^ w.length
        * UCPlanar.supNorm (P.square (3*R)) f)
      ≤ (A ^ w.length) * ((C * (w.length : ℝ) / R) ^ w.length
        * UCPlanar.supNorm (P.square (3*R)) f) := by
    refine mul_le_mul_of_nonneg_right (le_trans hAle hAn) ?_
    exact mul_nonneg hpow2 hsnn
  refine le_trans hstep1 ?_
  have hcollect : (A ^ w.length) * ((C * (w.length : ℝ) / R) ^ w.length)
      = ((A * C) * (w.length : ℝ) / R) ^ w.length := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hbase : ((A * C) * (w.length : ℝ) / R) ^ w.length
      ≤ (C₁ * (w.length : ℝ) / R) ^ w.length := by
    refine pow_le_pow_left₀ ?_ ?_ _
    · have hAC : (0:ℝ) ≤ A * C := mul_nonneg (by linarith) (le_of_lt hC0)
      positivity
    · have hACC₁ : A * C ≤ C₁ := le_max_left _ _
      gcongr
  calc (A ^ w.length) * ((C * (w.length : ℝ) / R) ^ w.length
        * UCPlanar.supNorm (P.square (3*R)) f)
      = ((A ^ w.length) * ((C * (w.length : ℝ) / R) ^ w.length))
          * UCPlanar.supNorm (P.square (3*R)) f := by ring
    _ = (((A * C) * (w.length : ℝ) / R) ^ w.length)
          * UCPlanar.supNorm (P.square (3*R)) f := by rw [hcollect]
    _ ≤ ((C₁ * (w.length : ℝ) / R) ^ w.length)
          * UCPlanar.supNorm (P.square (3*R)) f := mul_le_mul_of_nonneg_right hbase hsnn

end UCPlanar.Support
