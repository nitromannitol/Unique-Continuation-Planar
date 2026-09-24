/-
The killed walk of a conductance network, the discrete Dirichlet problem on a
finite set, and the Nash-Williams recurrence criterion.

The walk of the conductance `c` killed on leaving a finite set `C` has a finite
Green function, which solves the Dirichlet problem `Δ_c g = -δ_o` on `C` with
zero boundary.  Existence for that problem is finite-dimensional linear
algebra: the Laplacian on functions vanishing off `C` is injective by the
energy identity, hence surjective.  The Nash-Williams cutset bound then gives
`g(o) ≥ ½ ∑ 1/c(Π)` over any family of pairwise disjoint cutsets inside `C`,
so a network whose balls admit cutset families with divergent reciprocal sums
is recurrent.
-/
import UCPlanar.Support.LiouCHeat
import LatticeProb.Network.NashWilliams
import Mathlib.Order.Filter.AtTopBot.Basic

open scoped Classical ENNReal

namespace UCPlanar.Support

open LatticeProb.Network LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-! ### The killed walk -/

/-- The `k`-step transition probability of the `c`-walk killed on leaving
`C`: `killedCHeat G c C k x y = P_x(X_k = y, X_0, …, X_k ∈ C)`. -/
noncomputable def killedCHeat (G : SimpleGraph V) [G.LocallyFinite] (c : V → V → ℝ)
    (C : Set V) : ℕ → V → V → ℝ
  | 0 => fun x y => if x = y ∧ x ∈ C then 1 else 0
  | k + 1 => fun x y =>
      if x ∈ C then
        (∑ z ∈ G.neighborFinset x, c x z * killedCHeat G c C k z y) / weight G c x
      else 0

theorem killedCHeat_zero (c : V → V → ℝ) (C : Set V) (x y : V) :
    killedCHeat G c C 0 x y = if x = y ∧ x ∈ C then 1 else 0 := rfl

theorem killedCHeat_succ (c : V → V → ℝ) (C : Set V) (k : ℕ) (x y : V) :
    killedCHeat G c C (k + 1) x y
      = if x ∈ C then
          ∑ z ∈ G.neighborFinset x, (c x z / weight G c x) * killedCHeat G c C k z y
        else 0 := by
  simp only [killedCHeat]
  split_ifs with hx
  · rw [div_eq_mul_inv, Finset.sum_mul]
    exact Finset.sum_congr rfl fun z _ => by ring
  · rfl

theorem killedCHeat_nonneg {c : V → V → ℝ} (hc : IsCond G c)
    (hdeg : ∀ v : V, 0 < G.degree v) (C : Set V) :
    ∀ (k : ℕ) (x y : V), 0 ≤ killedCHeat G c C k x y := by
  intro k
  induction k with
  | zero =>
      intro x y
      rw [killedCHeat_zero]
      split_ifs <;> norm_num
  | succ k ih =>
      intro x y
      rw [killedCHeat_succ]
      split_ifs with hx
      · exact Finset.sum_nonneg fun z _ =>
          mul_nonneg (div_nonneg (hc.nonneg x z) (le_of_lt (weight_pos hc hdeg x))) (ih z y)
      · exact le_rfl

theorem killedCHeat_le_cHeat {c : V → V → ℝ} (hc : IsCond G c)
    (hdeg : ∀ v : V, 0 < G.degree v) (C : Set V) :
    ∀ (k : ℕ) (x y : V), killedCHeat G c C k x y ≤ cHeat G c k x y := by
  intro k
  induction k with
  | zero =>
      intro x y
      rw [killedCHeat_zero, cHeat_zero]
      by_cases hxy : x = y
      · subst hxy
        by_cases hx : x ∈ C <;> simp [hx]
      · simp [hxy]
  | succ k ih =>
      intro x y
      rw [killedCHeat_succ]
      split_ifs with hx
      · rw [cHeat_succ]
        exact Finset.sum_le_sum fun z _ =>
          mul_le_mul_of_nonneg_left (ih z y)
            (div_nonneg (hc.nonneg x z) (le_of_lt (weight_pos hc hdeg x)))
      · exact cHeat_nonneg hc hdeg (k + 1) x y

theorem killedCHeat_eq_zero_of_not_mem (c : V → V → ℝ) (C : Set V) {y : V} (hy : y ∉ C) :
    ∀ (k : ℕ) (x : V), killedCHeat G c C k x y = 0 := by
  intro k
  induction k with
  | zero =>
      intro x
      rw [killedCHeat_zero, if_neg]
      exact fun h => hy (h.1 ▸ h.2)
  | succ k ih =>
      intro x
      rw [killedCHeat_succ]
      split_ifs with hx
      · exact Finset.sum_eq_zero fun z _ => by rw [ih z, mul_zero]
      · rfl

theorem killedCHeat_eq_zero_of_start_not_mem (c : V → V → ℝ) (C : Set V) {x : V}
    (hx : x ∉ C) (k : ℕ) (y : V) : killedCHeat G c C k x y = 0 := by
  cases k with
  | zero =>
      rw [killedCHeat_zero, if_neg]
      exact fun h => hx h.2
  | succ k =>
      rw [killedCHeat_succ, if_neg hx]

end UCPlanar.Support

namespace UCPlanar.Support

open LatticeProb.Network LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-! ### The discrete Dirichlet problem on a finite set -/

/-- A function on `C` extended by zero. -/
noncomputable def extC (C : Finset V) (f : C → ℝ) : V → ℝ :=
  fun v => if h : v ∈ C then f ⟨v, h⟩ else 0

theorem extC_eq_zero_of_not_mem (C : Finset V) (f : C → ℝ) {v : V} (hv : v ∉ C) :
    extC C f v = 0 := by
  rw [extC, dif_neg hv]

theorem extC_apply (C : Finset V) (f : C → ℝ) {v : V} (hv : v ∈ C) :
    extC C f v = f ⟨v, hv⟩ := by
  rw [extC, dif_pos hv]

theorem extC_add (C : Finset V) (f g : C → ℝ) :
    extC C (f + g) = extC C f + extC C g := by
  funext v
  by_cases hv : v ∈ C <;> simp [extC, hv]

theorem extC_smul (C : Finset V) (a : ℝ) (f : C → ℝ) :
    extC C (a • f) = fun v => a * extC C f v := by
  funext v
  by_cases hv : v ∈ C <;> simp [extC, hv]

/-- The Laplacian as a linear map on functions on `C` (extended by zero). -/
noncomputable def bvpMap (G : SimpleGraph V) [G.LocallyFinite] (c : V → V → ℝ)
    (C : Finset V) : (C → ℝ) →ₗ[ℝ] (C → ℝ) where
  toFun f := fun x => ∑ y ∈ G.neighborFinset x,
    c x y * (extC C f y - extC C f x)
  map_add' f g := by
    funext x
    simp only [Pi.add_apply, extC_add]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  map_smul' a f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, extC_smul, RingHom.id_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring

theorem bvpMap_apply {c : V → V → ℝ} (C : Finset V) (f : C → ℝ) (x : C) :
    bvpMap G c C f x = netLaplacian G c (extC C f) x := rfl

theorem netLaplacian_sub (c : V → V → ℝ) (f g : V → ℝ) (x : V) :
    netLaplacian G c (f - g) x = netLaplacian G c f x - netLaplacian G c g x := by
  simp only [netLaplacian, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- The Laplacian on functions vanishing off a finite `C` is injective:
zero energy makes `extC C f` constant on adjacent pairs, hence constant, hence
zero. -/
theorem bvpMap_injective (hG : G.Connected) [Infinite V] {c : V → V → ℝ}
    (hc : IsCond G c) (C : Finset V) : Function.Injective (bvpMap G c C) := by
  rw [← LinearMap.ker_eq_bot (f := bvpMap G c C)]
  rw [LinearMap.ker_eq_bot']
  intro f hf
  have hlap : ∀ x ∈ C, netLaplacian G c (extC C f) x = 0 := by
    intro x hx
    rw [← bvpMap_apply C f ⟨x, hx⟩, hf]
    rfl
  have henergy : energyOn G c (nbhd G C) (extC C f) = 0 := by
    rw [energyOn_eq_neg_two_mul hc (nbhd G C) C _ (fun x hx => extC_eq_zero_of_not_mem C f hx)
      (subset_nbhd C) (fun x hx y hxy => mem_nbhd_of_adj hx hxy)]
    rw [Finset.sum_congr rfl (fun x hx => by rw [hlap x hx, mul_zero])]
    simp
  have hadj : ∀ x y : V, G.Adj x y → extC C f x = extC C f y := by
    intro x y hxy
    by_cases hx : x ∈ nbhd G C
    · have hzero : ∀ x ∈ nbhd G C, ∀ y ∈ G.neighborFinset x,
          c x y * (extC C f x - extC C f y) ^ 2 = 0 := by
        have h := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
          Finset.sum_nonneg fun y _ => mul_nonneg (hc.nonneg x y) (sq_nonneg _))).mp
          (by rw [energyOn_eq_sum] at henergy; exact henergy)
        intro x hx y hy
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun y _ =>
          mul_nonneg (hc.nonneg x y) (sq_nonneg _))).mp (h x hx) y hy
      have hxy' : y ∈ G.neighborFinset x := (SimpleGraph.mem_neighborFinset _ _ _).mpr hxy
      have hz := hzero x hx y hxy'
      have hcpos : 0 < c x y := hc.pos hxy
      have hsq : (extC C f x - extC C f y) ^ 2 = 0 := by
        rcases mul_eq_zero.mp hz with h | h
        · exact absurd h (ne_of_gt hcpos)
        · exact h
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
      linarith
    · have hyC : y ∉ C := by
        intro hyC
        exact hx (mem_nbhd_of_adj hyC hxy.symm)
      have hxC : x ∉ C := fun hxC => hx (subset_nbhd C hxC)
      rw [extC_eq_zero_of_not_mem C f hxC, extC_eq_zero_of_not_mem C f hyC]
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset C
  have hconst : ∀ x : V, extC C f x = extC C f z := by
    intro x
    obtain ⟨p⟩ := hG.preconnected x z
    clear hz
    induction p with
    | nil => rfl
    | cons hxy p ih => rw [hadj _ _ hxy]; exact ih
  funext x
  have hx := hconst x
  rw [extC_eq_zero_of_not_mem C f hz] at hx
  obtain ⟨x, hxC⟩ := x
  rw [extC_apply C f hxC] at hx
  exact hx

/-- The Dirichlet problem on a finite set has a solution: some `g` vanishing
off `C` has `Δ_c g = -δ_o` on `C`. -/
theorem bvp_exists (hG : G.Connected) [Infinite V] {c : V → V → ℝ} (hc : IsCond G c)
    (C : Finset V) {o : V} (_ho : o ∈ C) :
    ∃ g : V → ℝ, (∀ x, x ∉ C → g x = 0) ∧
      ∀ x ∈ C, netLaplacian G c g x = if x = o then -1 else 0 := by
  have hsurj := LinearMap.surjective_of_injective (bvpMap_injective hG hc C)
  obtain ⟨f, hf⟩ := hsurj (fun x : C => if (x : V) = o then -1 else 0)
  refine ⟨extC C f, fun x hx => extC_eq_zero_of_not_mem C f hx, fun x hx => ?_⟩
  rw [← bvpMap_apply C f ⟨x, hx⟩, hf]

/-- The solution of the discrete Dirichlet problem on `C` with source `o`. -/
noncomputable def bvpGreen (G : SimpleGraph V) [G.LocallyFinite] [Infinite V]
    (hG : G.Connected) {c : V → V → ℝ} (hc : IsCond G c)
    (C : Finset V) (o : V) (ho : o ∈ C) : V → ℝ :=
  (bvp_exists hG hc C ho).choose

theorem bvpGreen_eq_zero_of_not_mem (hG : G.Connected) [Infinite V] {c : V → V → ℝ}
    (hc : IsCond G c) (C : Finset V) {o : V} (ho : o ∈ C) {x : V} (hx : x ∉ C) :
    bvpGreen G hG hc C o ho x = 0 :=
  (bvp_exists hG hc C ho).choose_spec.1 x hx

theorem bvpGreen_laplacian (hG : G.Connected) [Infinite V] {c : V → V → ℝ}
    (hc : IsCond G c) (C : Finset V) {o : V} (ho : o ∈ C) {x : V} (hx : x ∈ C) :
    netLaplacian G c (bvpGreen G hG hc C o ho) x = if x = o then -1 else 0 :=
  (bvp_exists hG hc C ho).choose_spec.2 x hx

/-- Uniqueness for the discrete Dirichlet problem: two functions vanishing off
`C` with the same Laplacian on `C` agree. -/
theorem bvp_unique (hG : G.Connected) [Infinite V] {c : V → V → ℝ} (hc : IsCond G c)
    (C : Finset V) {g₁ g₂ : V → ℝ}
    (h₁ : ∀ x, x ∉ C → g₁ x = 0) (h₂ : ∀ x, x ∉ C → g₂ x = 0)
    (hlap : ∀ x ∈ C, netLaplacian G c g₁ x = netLaplacian G c g₂ x) :
    ∀ x, g₁ x = g₂ x := by
  intro x
  have hdiff : ∀ x ∈ C, netLaplacian G c (fun v => g₁ v - g₂ v) x = 0 := by
    intro x hx
    rw [show (fun v => g₁ v - g₂ v) = g₁ - g₂ from rfl, netLaplacian_sub, hlap x hx,
      sub_self]
  -- the difference is `extC C f` for `f` its restriction to `C`
  set f : C → ℝ := fun x => g₁ x - g₂ x with hf
  have hext : (fun v => g₁ v - g₂ v) = extC C f := by
    funext v
    by_cases hv : v ∈ C
    · rw [extC_apply C f hv]
    · rw [extC_eq_zero_of_not_mem C f hv, h₁ v hv, h₂ v hv, sub_self]
  have hker : bvpMap G c C f = 0 := by
    funext x
    rw [bvpMap_apply, ← hext]
    exact hdiff x x.2
  have h0 : f = 0 := bvpMap_injective hG hc C (by rw [hker, LinearMap.map_zero])
  by_cases hx : x ∈ C
  · have hxz := congrFun h0 ⟨x, hx⟩
    simp only [Pi.zero_apply, hf] at hxz
    linarith [hxz]
  · rw [h₁ x hx, h₂ x hx]

/-- The energy of the Dirichlet solution is twice its value at the source. -/
theorem bvpGreen_energy (hG : G.Connected) [Infinite V] {c : V → V → ℝ} (hc : IsCond G c)
    (C : Finset V) {o : V} (ho : o ∈ C) :
    energyOn G c (nbhd G C) (bvpGreen G hG hc C o ho) = 2 * bvpGreen G hG hc C o ho o := by
  rw [energyOn_eq_neg_two_mul hc (nbhd G C) C (bvpGreen G hG hc C o ho)
    (fun x hx => bvpGreen_eq_zero_of_not_mem hG hc C ho hx) (subset_nbhd C)
    (fun x hx y hxy => mem_nbhd_of_adj hx hxy)]
  rw [Finset.sum_congr rfl (fun x hx => by rw [bvpGreen_laplacian hG hc C ho hx])]
  simp only [mul_ite, mul_neg, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' C o _, if_pos ho]
  ring

/-! ### The minimum principle for superharmonic functions -/

/-- A function superharmonic on a finite `C` and zero off `C` is nonnegative. -/
theorem nonneg_of_superharmonic (hG : G.Connected) [Infinite V] {c : V → V → ℝ}
    (hc : IsCond G c) (C : Finset V) (f : V → ℝ)
    (hsup : ∀ x ∈ C, netLaplacian G c f x ≤ 0) (hout : ∀ x, x ∉ C → f x = 0) :
    ∀ x, 0 ≤ f x := by
  by_contra hcon
  obtain ⟨x, hx⟩ := not_forall.mp hcon
  rw [not_le] at hx
  have hxC : x ∈ C := by
    by_contra h
    rw [hout x h] at hx
    exact lt_irrefl _ hx
  obtain ⟨b, hbC, hbmin⟩ := Finset.exists_min_image C f ⟨x, hxC⟩
  have hfb : f b < 0 := lt_of_le_of_lt (hbmin x hxC) hx
  have hmin : ∀ y : V, f b ≤ f y := by
    intro y
    by_cases hy : y ∈ C
    · exact hbmin y hy
    · rw [hout y hy]
      exact le_of_lt hfb
  have hstep : ∀ y : V, y ∈ C → f y = f b → ∀ z : V, G.Adj y z → f z = f b := by
    intro y hyC hyb z hyz
    have hterms : ∀ w ∈ G.neighborFinset y, 0 ≤ c y w * (f w - f y) := by
      intro w _
      exact mul_nonneg (hc.nonneg y w) (by rw [hyb]; exact sub_nonneg.mpr (hmin w))
    have hsum : ∑ w ∈ G.neighborFinset y, c y w * (f w - f y) = 0 :=
      le_antisymm (hsup y hyC) (Finset.sum_nonneg hterms)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hsum z
      ((SimpleGraph.mem_neighborFinset _ _ _).mpr hyz)
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h (hc.pos hyz).ne'
    · rw [← hyb]
      linarith
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset C
  obtain ⟨p⟩ := hG.preconnected b z
  have hwalk : ∀ {u v : V} (p : G.Walk u v), u ∈ C → f u = f b → f v = f b := by
    intro u v p
    induction p with
    | nil => intro _ h; exact h
    | @cons u v w hadj p ih =>
        intro huC hfu
        have huv := hstep u huC hfu v hadj
        refine ih ?_ huv
        by_contra hvC
        rw [hout v hvC] at huv
        linarith
  have := hwalk p hbC rfl
  rw [hout z hz] at this
  linarith

end UCPlanar.Support

namespace UCPlanar.Support

open LatticeProb.Network LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-! ### The killed Green function -/

/-- The partial sums of the killed Green function. -/
noncomputable def killedPartial (G : SimpleGraph V) [G.LocallyFinite] (c : V → V → ℝ)
    (C : Set V) (N : ℕ) (x o : V) : ℝ :=
  ∑ k ∈ Finset.range N, killedCHeat G c C k x o

/-- The one-step recursion of the killed partial sums. -/
theorem killedPartial_succ {c : V → V → ℝ} (C : Set V) (N : ℕ) {x o : V} (hx : x ∈ C) :
    killedPartial G c C (N + 1) x o
      = (if x = o then 1 else 0)
        + ∑ z ∈ G.neighborFinset x, (c x z / weight G c x) * killedPartial G c C N z o := by
  rw [killedPartial, Finset.sum_range_succ']
  have h0 : killedCHeat G c C 0 x o = if x = o then 1 else 0 := by
    rw [killedCHeat_zero]
    by_cases hxo : x = o
    · rw [if_pos ⟨hxo, hx⟩, if_pos hxo]
    · rw [if_neg (fun h => hxo h.1), if_neg hxo]
  rw [h0, add_comm]
  congr 1
  rw [Finset.sum_congr rfl (fun k _ => killedCHeat_succ c C k x o)]
  simp only [if_pos hx]
  rw [Finset.sum_comm]
  simp only [killedPartial, Finset.mul_sum]

/-- The killed Green function of the `c`-walk on `C`. -/
noncomputable def killedGreenSum (G : SimpleGraph V) [G.LocallyFinite] (c : V → V → ℝ)
    (C : Set V) (x o : V) : ℝ :=
  ∑' k : ℕ, killedCHeat G c C k x o

/-- The Dirichlet solution dominates the normalized killed partial sums. -/
theorem killedPartial_le {c : V → V → ℝ} (hG : G.Connected) [Infinite V]
    (hc : IsCond G c) (hdeg : ∀ v : V, 0 < G.degree v)
    (C : Finset V) {o : V} (ho : o ∈ C) (N : ℕ) (x : V) :
    killedPartial G c (C : Set V) N x o
      ≤ weight G c o * bvpGreen G hG hc C o ho x := by
  have hsup : ∀ x ∈ C, netLaplacian G c
      (fun v => bvpGreen G hG hc C o ho v
        - (weight G c o)⁻¹ * killedPartial G c (C : Set V) N v o) x ≤ 0 := by
    intro x hx
    have hwt : weight G c o ≠ 0 := ne_of_gt (weight_pos hc hdeg o)
    have hrec := killedPartial_succ (G := G) (c := c) (o := o) (C : Set V) N hx
    have hlapP : netLaplacian G c (killedPartial G c (C : Set V) N · o) x
        = weight G c x * (killedCHeat G c (C : Set V) N x o - (if x = o then 1 else 0)) := by
      rw [netLaplacian]
      have h1 : (∑ y ∈ G.neighborFinset x,
            c x y * (killedPartial G c (C : Set V) N y o
              - killedPartial G c (C : Set V) N x o))
          = (∑ y ∈ G.neighborFinset x, c x y * killedPartial G c (C : Set V) N y o)
            - weight G c x * killedPartial G c (C : Set V) N x o := by
        rw [weight, Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun y _ => by ring
      rw [h1]
      have h2 : (∑ y ∈ G.neighborFinset x, c x y * killedPartial G c (C : Set V) N y o)
          = weight G c x
            * (∑ y ∈ G.neighborFinset x,
                (c x y / weight G c x) * killedPartial G c (C : Set V) N y o) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y hy => ?_
        have hwx : weight G c x ≠ 0 := ne_of_gt (weight_pos hc hdeg x)
        field_simp
      rw [h2]
      have h3 : (∑ y ∈ G.neighborFinset x,
            (c x y / weight G c x) * killedPartial G c (C : Set V) N y o)
          = killedPartial G c (C : Set V) (N + 1) x o - (if x = o then 1 else 0) := by
        rw [hrec]; ring
      rw [h3]
      rw [show killedPartial G c (C : Set V) (N + 1) x o
          = killedPartial G c (C : Set V) N x o + killedCHeat G c (C : Set V) N x o from
        by rw [killedPartial, killedPartial, Finset.sum_range_succ]]
      ring
    rw [show (fun v => bvpGreen G hG hc C o ho v
          - (weight G c o)⁻¹ * killedPartial G c (C : Set V) N v o)
        = bvpGreen G hG hc C o ho
          - fun v => (weight G c o)⁻¹ * killedPartial G c (C : Set V) N v o from rfl]
    rw [netLaplacian_sub, netLaplacian_smul, bvpGreen_laplacian hG hc C ho hx, hlapP]
    by_cases hxo : x = o
    · subst hxo
      rw [if_pos rfl, if_pos rfl, inv_mul_cancel_left₀ hwt]
      have hle : 0 ≤ killedCHeat G c (C : Set V) N x x := killedCHeat_nonneg hc hdeg _ N x x
      linarith
    · rw [if_neg hxo, if_neg hxo, sub_zero]
      have hle1 : 0 ≤ killedCHeat G c (C : Set V) N x o := killedCHeat_nonneg hc hdeg _ N x o
      have hle2 : 0 ≤ weight G c x := le_of_lt (weight_pos hc hdeg x)
      have hle3 : 0 ≤ (weight G c o)⁻¹ := inv_nonneg.mpr (le_of_lt (weight_pos hc hdeg o))
      have hnn : 0 ≤ (weight G c o)⁻¹ * (weight G c x * killedCHeat G c (C : Set V) N x o) :=
        mul_nonneg hle3 (mul_nonneg hle2 hle1)
      linarith
  have hout : ∀ x, x ∉ C → bvpGreen G hG hc C o ho x
      - (weight G c o)⁻¹ * killedPartial G c (C : Set V) N x o = 0 := by
    intro x hx
    rw [bvpGreen_eq_zero_of_not_mem hG hc C ho hx]
    have : killedPartial G c (C : Set V) N x o = 0 := by
      rw [killedPartial]
      exact Finset.sum_eq_zero fun k _ => killedCHeat_eq_zero_of_start_not_mem c _ hx k o
    rw [this, mul_zero, sub_self]
  have hnn := nonneg_of_superharmonic hG hc C _ hsup hout x
  have hwt : 0 < weight G c o := weight_pos hc hdeg o
  have := mul_le_mul_of_nonneg_left hnn (le_of_lt hwt)
  rw [mul_zero, mul_sub, mul_inv_cancel_left₀ (ne_of_gt hwt), sub_nonneg] at this
  exact this

theorem summable_killedCHeat {c : V → V → ℝ} (hG : G.Connected) [Infinite V]
    (hc : IsCond G c) (hdeg : ∀ v : V, 0 < G.degree v)
    (C : Finset V) {o : V} (ho : o ∈ C) (x : V) :
    Summable fun k => killedCHeat G c (C : Set V) k x o :=
  summable_of_sum_range_le (fun k => killedCHeat_nonneg hc hdeg _ k x o)
    (fun N => killedPartial_le hG hc hdeg C ho N x)

/-- The killed Green function is at most `weight G c o` times the Dirichlet
solution. -/
theorem killedGreenSum_le {c : V → V → ℝ} (hG : G.Connected) [Infinite V]
    (hc : IsCond G c) (hdeg : ∀ v : V, 0 < G.degree v)
    (C : Finset V) {o : V} (ho : o ∈ C) (x : V) :
    killedGreenSum G c (C : Set V) x o ≤ weight G c o * bvpGreen G hG hc C o ho x := by
  have hs := summable_killedCHeat hG hc hdeg C ho x
  exact le_of_tendsto (hs.hasSum.tendsto_sum_nat)
    (Filter.Eventually.of_forall fun N => killedPartial_le hG hc hdeg C ho N x)

/-- The killed Green function solves the Dirichlet problem. -/
theorem killedGreenSum_eq {c : V → V → ℝ} (hG : G.Connected) [Infinite V]
    (hc : IsCond G c) (hdeg : ∀ v : V, 0 < G.degree v)
    (C : Finset V) {o : V} (ho : o ∈ C) :
    killedGreenSum G c (C : Set V) o o
      = weight G c o * bvpGreen G hG hc C o ho o := by
  have hs : ∀ x, Summable fun k => killedCHeat G c (C : Set V) k x o :=
    fun x => summable_killedCHeat hG hc hdeg C ho x
  have h0 : ∀ x, Filter.Tendsto (fun N => killedPartial G c (C : Set V) N x o) Filter.atTop
      (nhds (killedGreenSum G c (C : Set V) x o)) :=
    fun x => (hs x).hasSum.tendsto_sum_nat
  -- the limit identity: `kG x = δ + P(kG) x` on `C`
  have hid : ∀ x ∈ C, killedGreenSum G c (C : Set V) x o
      = (if x = o then 1 else 0)
        + ∑ z ∈ G.neighborFinset x, (c x z / weight G c x)
            * killedGreenSum G c (C : Set V) z o := by
    intro x hx
    have hL : Filter.Tendsto (fun N => killedPartial G c (C : Set V) (N + 1) x o) Filter.atTop
        (nhds (killedGreenSum G c (C : Set V) x o)) :=
      (Filter.tendsto_add_atTop_iff_nat 1).mpr (h0 x)
    have hR : Filter.Tendsto (fun N => (if x = o then 1 else 0)
        + ∑ z ∈ G.neighborFinset x, (c x z / weight G c x)
            * killedPartial G c (C : Set V) N z o) Filter.atTop
        (nhds ((if x = o then 1 else 0)
          + ∑ z ∈ G.neighborFinset x, (c x z / weight G c x)
              * killedGreenSum G c (C : Set V) z o)) := by
      refine Filter.Tendsto.const_add _ ?_
      refine tendsto_finsetSum _ fun z _ => ?_
      exact Filter.Tendsto.const_mul _ (h0 z)
    have hL' : ∀ N : ℕ, killedPartial G c (C : Set V) (N + 1) x o
        = (if x = o then 1 else 0)
          + ∑ z ∈ G.neighborFinset x, (c x z / weight G c x)
              * killedPartial G c (C : Set V) N z o :=
      fun N => killedPartial_succ (C : Set V) N hx
    exact tendsto_nhds_unique (by simpa only [hL'] using hL) hR
  -- the Laplacian of the normalized killed Green function
  have hvan : ∀ x, x ∉ C → (weight G c o)⁻¹ * killedGreenSum G c (C : Set V) x o = 0 := by
    intro x hx
    have : killedGreenSum G c (C : Set V) x o = 0 := by
      rw [killedGreenSum]
      convert tsum_zero with k
      exact killedCHeat_eq_zero_of_start_not_mem c _ hx k o
    rw [this, mul_zero]
  have hlap : ∀ x ∈ C, netLaplacian G c
      (fun v => (weight G c o)⁻¹ * killedGreenSum G c (C : Set V) v o) x
      = if x = o then -1 else 0 := by
    intro x hx
    rw [netLaplacian_smul]
    have hwt : weight G c x ≠ 0 := ne_of_gt (weight_pos hc hdeg x)
    have h1 : netLaplacian G c (killedGreenSum G c (C : Set V) · o) x
        = -weight G c x * (if x = o then 1 else 0) := by
      rw [netLaplacian]
      have h2 : (∑ y ∈ G.neighborFinset x,
            c x y * (killedGreenSum G c (C : Set V) y o
              - killedGreenSum G c (C : Set V) x o))
          = (∑ y ∈ G.neighborFinset x, c x y * killedGreenSum G c (C : Set V) y o)
            - weight G c x * killedGreenSum G c (C : Set V) x o := by
        rw [weight, Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun y _ => by ring
      rw [h2]
      have h3 : (∑ y ∈ G.neighborFinset x, c x y * killedGreenSum G c (C : Set V) y o)
          = weight G c x
            * (∑ y ∈ G.neighborFinset x,
                (c x y / weight G c x) * killedGreenSum G c (C : Set V) y o) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y hy => ?_
        field_simp
      rw [h3, hid x hx]
      ring
    rw [h1]
    by_cases hxo : x = o
    · subst hxo
      rw [if_pos rfl, if_pos rfl, mul_one, mul_neg, inv_mul_cancel₀ hwt]
    · simp [if_neg hxo]
  have heq := bvp_unique hG hc C hvan (fun x hx => bvpGreen_eq_zero_of_not_mem hG hc C ho hx)
    (fun x hx => by rw [hlap x hx, bvpGreen_laplacian hG hc C ho hx]) o
  have hwt : weight G c o ≠ 0 := ne_of_gt (weight_pos hc hdeg o)
  have := heq
  rw [eq_comm] at this
  calc killedGreenSum G c (C : Set V) o o
      = weight G c o * ((weight G c o)⁻¹ * killedGreenSum G c (C : Set V) o o) := by
        rw [mul_inv_cancel_left₀ hwt]
    _ = weight G c o * bvpGreen G hG hc C o ho o := by rw [this]

/-- The Green function of the free walk is at least `weight G c o` times the
Dirichlet solution on any finite set containing the source. -/
theorem ofReal_weight_mul_bvpGreen_le_cGreen {c : V → V → ℝ} (hG : G.Connected)
    [Infinite V] (hc : IsCond G c) (hdeg : ∀ v : V, 0 < G.degree v)
    (C : Finset V) {o : V} (ho : o ∈ C) :
    ENNReal.ofReal (weight G c o * bvpGreen G hG hc C o ho o) ≤ cGreen G c o o := by
  rw [← killedGreenSum_eq hG hc hdeg C ho]
  rw [cGreen_eq_tsum, killedGreenSum, ENNReal.ofReal_tsum_of_nonneg
    (fun k => killedCHeat_nonneg hc hdeg _ k o o) (summable_killedCHeat hG hc hdeg C ho o)]
  exact ENNReal.tsum_le_tsum (fun k =>
    ENNReal.ofReal_le_ofReal (killedCHeat_le_cHeat hc hdeg _ k o o))

/-! ### Nash-Williams -/

theorem mem_pairs {S : Finset V} {p : V × V} :
    p ∈ pairs G S ↔ p.1 ∈ S ∧ G.Adj p.1 p.2 := by
  simp only [pairs, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨hx, (SimpleGraph.mem_neighborFinset _ _ _).mp hy⟩
  · rintro ⟨hx, hxy⟩
    exact ⟨p.1, hx, p.2, (SimpleGraph.mem_neighborFinset _ _ _).mpr hxy, rfl⟩

/-- The energy of the current of `f` is the energy of `f`. -/
theorem flowEnergyOn_current {c : V → V → ℝ} (hc : IsCond G c) (S : Finset V) (f : V → ℝ) :
    flowEnergyOn G c S (current G c f) = energyOn G c S f := by
  rw [flowEnergyOn, energyOn_eq_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y hy => ?_
  have hcpos : 0 < c x y := hc.pos ((SimpleGraph.mem_neighborFinset _ _ _).mp hy)
  rw [current]
  field_simp

/-- The Nash-Williams bound for the Dirichlet solution: any family of pairwise
disjoint cutsets inside `C`, each carrying a unit of the current, has its
reciprocal conductance sum bounded by twice the value at the source. -/
theorem cutset_sum_le_two_mul_bvpGreen {c : V → V → ℝ} (hG : G.Connected) [Infinite V]
    (hc : IsCond G c) (C : Finset V) {o : V} (ho : o ∈ C)
    (K : Finset ℕ) (Cut : ℕ → Finset (V × V))
    (hsub : ∀ k ∈ K, Cut k ⊆ pairs G (nbhd G C))
    (hdisj : (K : Set ℕ).PairwiseDisjoint Cut)
    (hcut : ∀ k ∈ K,
      1 ≤ ∑ p ∈ Cut k, current G c (bvpGreen G hG hc C o ho) p.1 p.2) :
    ∑ k ∈ K, 1 / (∑ p ∈ Cut k, c p.1 p.2)
      ≤ 2 * bvpGreen G hG hc C o ho o := by
  have hpos : ∀ k ∈ K, ∀ p ∈ Cut k, 0 < c p.1 p.2 := by
    intro k hk p hp
    exact hc.pos ((mem_pairs.mp (hsub k hk hp)).2)
  have hnw := nashWilliams hc (nbhd G C) (current G c (bvpGreen G hG hc C o ho))
    K Cut hsub hdisj hpos hcut
  rw [flowEnergyOn_current hc, bvpGreen_energy hG hc C ho] at hnw
  exact hnw

/-- The recurrence criterion: if finite sets containing `o` make
`weight G c o` times the Dirichlet value at `o` arbitrarily large, the network
is recurrent. -/
theorem networkRecurrent_of_forall_exists {c : V → V → ℝ} (hG : G.Connected) [Infinite V]
    (hc : IsCond G c) (hdeg : ∀ v : V, 0 < G.degree v) (o : V)
    (h : ∀ B : ℝ, ∃ C : Finset V, ∃ ho : o ∈ C,
      B ≤ weight G c o * bvpGreen G hG hc C o ho o) :
    NetworkRecurrent G c o := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  obtain ⟨C, ho, hB⟩ := h (r + 1)
  calc (r : ℝ≥0∞)
      = ENNReal.ofReal (r : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
    _ ≤ ENNReal.ofReal (weight G c o * bvpGreen G hG hc C o ho o) :=
        ENNReal.ofReal_le_ofReal (le_trans (by simp) hB)
    _ ≤ cGreen G c o o := ofReal_weight_mul_bvpGreen_le_cGreen hG hc hdeg C ho

end UCPlanar.Support
