/-
The discrete Caccioppoli inequality for a harmonic function on a finite
weighted graph, with the periodic-conductance hypotheses explicit.
-/
import UCPlanar.Support.Poly.Basic
import LatticeProb.Network.Variational

open scoped BigOperators Classical
set_option autoImplicit false

namespace UCPlanar.Support

theorem caccioppoli_pointwise (a b u v : ℝ) :
    (a - b) ^ 2 * u ^ 2
      ≤ 2 * (a - b) * (a * u ^ 2 - b * v ^ 2) + 4 * (a ^ 2 + b ^ 2) * (u - v) ^ 2 := by
  nlinarith [sq_nonneg ((a - b) * v + (a + b) * (u - v)), sq_nonneg (2 * a - b),
    sq_nonneg a, sq_nonneg b, sq_nonneg (u - v)]

theorem caccioppoli {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    {c : V → V → ℝ} (hc : LatticeProb.Network.IsCond G c)
    (S B : Finset V) (f η : V → ℝ)
    (hf : ∀ x ∈ S, LatticeProb.Network.netLaplacian G c f x = 0)
    (hη : ∀ x, x ∉ B → η x = 0) (hBS : B ⊆ S)
    (hnb : ∀ x ∈ B, ∀ y, G.Adj x y → y ∈ S) :
    ∑ x ∈ S, ∑ y ∈ G.neighborFinset x, c x y * (f x - f y) ^ 2 * η x ^ 2
      ≤ 4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
          c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
  have hg : ∀ x, x ∉ B → f x * η x ^ 2 = 0 := fun x hx => by rw [hη x hx]; ring
  have hform := LatticeProb.Network.formOn_eq_neg_two_mul hc S B f
    (fun x => f x * η x ^ 2) hg hBS hnb
  have hharm : ∑ x ∈ B, f x * η x ^ 2 * LatticeProb.Network.netLaplacian G c f x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [hf x (hBS hx)]
    ring
  rw [hharm, mul_zero] at hform
  have hpt : ∀ x ∈ S, ∀ y ∈ G.neighborFinset x,
      c x y * (f x - f y) ^ 2 * η x ^ 2
        ≤ 2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2))
          + 4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2) := by
    intro x _ y _
    have hc0 := hc.nonneg x y
    nlinarith [caccioppoli_pointwise (f x) (f y) (η x) (η y),
      mul_nonneg hc0 (sq_nonneg (f x - f y)), mul_nonneg hc0 (sq_nonneg (η x - η y))]
  calc ∑ x ∈ S, ∑ y ∈ G.neighborFinset x, c x y * (f x - f y) ^ 2 * η x ^ 2
      ≤ ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
          (2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2))
            + 4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2)) :=
        Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => hpt x hx y hy
    _ = 2 * LatticeProb.Network.formOn G c S f (fun x => f x * η x ^ 2)
          + 4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
              c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
        have h1 : (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
              2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2)))
            = 2 * LatticeProb.Network.formOn G c S f (fun x => f x * η x ^ 2) := by
          simp only [LatticeProb.Network.formOn, Finset.mul_sum]
        have h2 : (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
              4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2))
            = 4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
                c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
          simp only [Finset.mul_sum]
        rw [show (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
              (2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2))
                + 4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2)))
            = (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
                2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2)))
              + ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
                  4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2) from by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun x _ => Finset.sum_add_distrib]
        rw [h1, h2]
    _ = 4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
          c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
        rw [hform]; ring

theorem moser_mean_value {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    {c : V → V → ℝ} (hc : LatticeProb.Network.IsCond G c)
    (f : V → ℝ) (x₀ : V)
    (hx₀ : LatticeProb.Network.weight G c x₀ ≠ 0)
    (hf : LatticeProb.Network.netLaplacian G c f x₀ = 0) :
    f x₀ ^ 2 ≤ (∑ y ∈ G.neighborFinset x₀, c x₀ y * f y ^ 2)
      / LatticeProb.Network.weight G c x₀ := by
  rw [LatticeProb.Network.harmonic_iff_mean f hx₀] at hf
  rw [hf]
  set W := LatticeProb.Network.weight G c x₀ with hWdef
  have hW : 0 < W :=
    lt_of_le_of_ne (Finset.sum_nonneg fun y _ => hc.nonneg x₀ y) (Ne.symm hx₀)
  have hcs : (∑ y ∈ G.neighborFinset x₀, c x₀ y * f y) ^ 2
      ≤ W * ∑ y ∈ G.neighborFinset x₀, c x₀ y * f y ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (G.neighborFinset x₀)
      (fun y => Real.sqrt (c x₀ y)) (fun y => Real.sqrt (c x₀ y) * f y)
    rw [hWdef, LatticeProb.Network.weight]
    have e1 : (∑ y ∈ G.neighborFinset x₀, Real.sqrt (c x₀ y) * (Real.sqrt (c x₀ y) * f y))
        = ∑ y ∈ G.neighborFinset x₀, c x₀ y * f y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [← mul_assoc, ← sq, Real.sq_sqrt (hc.nonneg x₀ y)]
    have e2 : (∑ y ∈ G.neighborFinset x₀, Real.sqrt (c x₀ y) ^ 2)
        = ∑ y ∈ G.neighborFinset x₀, c x₀ y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Real.sq_sqrt (hc.nonneg x₀ y)]
    have e3 : (∑ y ∈ G.neighborFinset x₀, (Real.sqrt (c x₀ y) * f y) ^ 2)
        = ∑ y ∈ G.neighborFinset x₀, c x₀ y * f y ^ 2 := by
      apply Finset.sum_congr rfl
      intro y _
      rw [mul_pow, Real.sq_sqrt (hc.nonneg x₀ y)]
    rw [e1, e2, e3] at h
    exact h
  rw [div_pow, div_le_div_iff₀ (by positivity) hW]
  nlinarith [hcs]

theorem moser_estimate {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    {c : V → V → ℝ} (hc : LatticeProb.Network.IsCond G c)
    (B : Finset V) (f : V → ℝ) (w : ℝ) (hw : 0 < w)
    (hf : ∀ x ∈ B, LatticeProb.Network.netLaplacian G c f x = 0)
    (hweight : ∀ x ∈ B, w ≤ LatticeProb.Network.weight G c x) :
    ∑ x ∈ B, f x ^ 2
      ≤ (1 / w) * ∑ x ∈ B, ∑ y ∈ G.neighborFinset x, c x y * f y ^ 2 := by
  have h : ∀ x ∈ B, f x ^ 2
      ≤ (∑ y ∈ G.neighborFinset x, c x y * f y ^ 2) / LatticeProb.Network.weight G c x :=
    fun x hx => UCPlanar.Support.moser_mean_value hc f x
      (ne_of_gt (lt_of_lt_of_le hw (hweight x hx))) (hf x hx)
  calc ∑ x ∈ B, f x ^ 2
      ≤ ∑ x ∈ B, (∑ y ∈ G.neighborFinset x, c x y * f y ^ 2)
          / LatticeProb.Network.weight G c x := Finset.sum_le_sum h
    _ ≤ ∑ x ∈ B, (1 / w) * ∑ y ∈ G.neighborFinset x, c x y * f y ^ 2 := by
        refine Finset.sum_le_sum fun x hx => ?_
        have hnum : 0 ≤ ∑ y ∈ G.neighborFinset x, c x y * f y ^ 2 :=
          Finset.sum_nonneg fun y _ => mul_nonneg (hc.nonneg x y) (sq_nonneg _)
        rw [div_le_iff₀ (lt_of_lt_of_le hw (hweight x hx))]
        rw [one_div_mul_eq_div]
        rw [div_mul_eq_mul_div, le_div_iff₀ hw]
        nlinarith [hweight x hx, hnum]
    _ = (1 / w) * ∑ x ∈ B, ∑ y ∈ G.neighborFinset x, c x y * f y ^ 2 := by
        rw [Finset.mul_sum]

theorem moser_l2_step {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    {c : V → V → ℝ} (hc : LatticeProb.Network.IsCond G c)
    (B : Finset V) (f : V → ℝ) (K w Ssup : ℝ) (hw : 0 < w) (hK : 0 ≤ K)
    (hf : ∀ x ∈ B, LatticeProb.Network.netLaplacian G c f x = 0)
    (hweight : ∀ x ∈ B, w ≤ LatticeProb.Network.weight G c x)
    (hcond : ∀ x ∈ B, ∑ y ∈ G.neighborFinset x, c x y ≤ K)
    (hfsup : ∀ y, f y ^ 2 ≤ Ssup ^ 2) :
    ∀ x ∈ B, f x ^ 2 ≤ (K / w) * Ssup ^ 2 := by
  intro x hx
  have hW : 0 < LatticeProb.Network.weight G c x := lt_of_lt_of_le hw (hweight x hx)
  have hmv := UCPlanar.Support.moser_mean_value hc f x (ne_of_gt hW) (hf x hx)
  have hnum : ∑ y ∈ G.neighborFinset x, c x y * f y ^ 2
      ≤ (∑ y ∈ G.neighborFinset x, c x y) * Ssup ^ 2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun y hy => by
      have hy2 := hfsup y
      nlinarith [hc.nonneg x y, hy2, sq_nonneg (f y), sq_nonneg Ssup]
  have hS : 0 ≤ Ssup ^ 2 := sq_nonneg Ssup
  calc f x ^ 2
      ≤ (∑ y ∈ G.neighborFinset x, c x y * f y ^ 2) / LatticeProb.Network.weight G c x := hmv
    _ ≤ ((∑ y ∈ G.neighborFinset x, c x y) * Ssup ^ 2)
          / LatticeProb.Network.weight G c x := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt hW)
    _ ≤ (K * Ssup ^ 2) / w := by
        rw [div_le_div_iff₀ hW hw]
        have h1 := hcond x hx
        have hKS : 0 ≤ K * Ssup ^ 2 := mul_nonneg hK hS
        have hstep1 : (∑ y ∈ G.neighborFinset x, c x y) * Ssup ^ 2 ≤ K * Ssup ^ 2 :=
          mul_le_mul_of_nonneg_right h1 hS
        have hstep2 : (∑ y ∈ G.neighborFinset x, c x y) * Ssup ^ 2 * w
            ≤ K * Ssup ^ 2 * w := mul_le_mul_of_nonneg_right hstep1 (le_of_lt hw)
        have hstep3 : K * Ssup ^ 2 * w ≤ K * Ssup ^ 2 * LatticeProb.Network.weight G c x :=
          mul_le_mul_of_nonneg_left (hweight x hx) hKS
        linarith
    _ = (K / w) * Ssup ^ 2 := by ring

end UCPlanar.Support
