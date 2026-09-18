/- Step 2 of Section 4: the rescaling that turns a coarse exponential bound into `exp (A √ε n)`. -/
import UCPlanar.Support.ZeroLower
import UCPlanar.Support.ZeroMax
import UCPlanar.Support.FiniteDomains
import Mathlib

open scoped BigOperators Classical

namespace UCPlanar.Support

/-- **Step 2 of Section 4: improving the exponent by rescaling.**  Granting the coarse
exponential bound of Step 1 at every centre and every radius above a geometric minimum `r₀`,
the bound on `B_n` improves to `exp (A √ε n)`.

The rescaling is applied at each point `x ∈ B_n` with the ball centred at `x` itself, so no
covering count enters; the admissible radius is `max r₀ ⌈δ √ε n⌉`, where `δ` compares the
quadratic upper and lower bounds on ball cardinality.  Scales at which the exceptional count
falls below `n` are handled instead by the maximum principle, which is what keeps the minimum
radius `max (2 r₀) 4` free of the ellipticity ratio. -/
theorem uniformlyBounded_of_coarse {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (r₀ : ℕ) (hr₀ : 0 < r₀) (Θ : ℝ) (ε₁ a : ℝ) (hε₁ : 0 < ε₁) (ha : 0 < a)
    (coarse : ∀ lam : ℝ, 0 < lam → ∀ c : V → V → ℝ,
        LatticeProb.Network.IsCond P.graph c →
        UCPlanar.UniformlyElliptic P.graph c lam (Θ*lam) →
        ∀ (z : V) (r : ℕ), r₀ ≤ r → ∀ f : V → ℝ,
          LatticeProb.Network.HarmonicOn P.graph c f
            (LatticeProb.Graph.closedBall P.graph z (2*r)) →
          ((UCPlanar.exceptionalCount (P.ball z (2*r)) f 1 : ℝ)
            ≤ ε₁ * (P.ball z (2*r)).card) →
          ∀ y ∈ P.ball z r, |f y| ≤ Real.exp (a * r)) :
    ∃ ε₀ A : ℝ, 0 < ε₀ ∧ 0 < A ∧
      ∀ lam : ℝ, 0 < lam → ∀ c : V → V → ℝ,
        LatticeProb.Network.IsCond P.graph c →
        UCPlanar.UniformlyElliptic P.graph c lam (Θ*lam) →
        ∀ (o : V) (n : ℕ), max (2*r₀) 4 ≤ n → ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ → ∀ f : V → ℝ,
          LatticeProb.Network.HarmonicOn P.graph c f
            (LatticeProb.Graph.closedBall P.graph o (2*n)) →
          ((UCPlanar.exceptionalCount (P.ball o (2*n)) f 1 : ℝ)
            ≤ ε * (P.ball o (2*n)).card) →
          ∀ x ∈ P.ball o n, |f x| ≤ Real.exp (A * Real.sqrt ε * n) := by
  classical
  obtain ⟨C₀, hC₀, hup⟩ := exists_ball_card_bound P
  obtain ⟨c₀, hc₀, hlow⟩ := exists_ball_card_lower P
  set δ : ℝ := Real.sqrt (9*C₀/(4*ε₁*c₀)) with hδdef
  have hδ0 : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  have hδsq : δ^2 = 9*C₀/(4*ε₁*c₀) := Real.sq_sqrt (by positivity)
  have hsqC₀ : 0 < Real.sqrt C₀ := Real.sqrt_pos.mpr hC₀
  refine ⟨1/(16*δ^2), a*δ + 3*a*((r₀:ℝ)+1)*Real.sqrt C₀, by positivity, by positivity, ?_⟩
  intro lam hlam c hc hell o n hn ε hε hεlt f hharm hcount x hx
  set A : ℝ := a*δ + 3*a*((r₀:ℝ)+1)*Real.sqrt C₀ with hA
  have hA0 : 0 < A := by rw [hA]; positivity
  have hn4 : 4 ≤ n := le_trans (le_max_right _ _) hn
  have hnr₀ : 2*r₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn1R : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hsqε : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hharm' : ∀ z ∈ P.ball o (2*n),
      LatticeProb.Network.netLaplacian P.graph c f z = 0 := by
    intro z hz
    refine hharm z ?_
    rw [← coe_ball]
    exact_mod_cast hz
  set E : ℕ := UCPlanar.exceptionalCount (P.ball o (2*n)) f 1 with hE
  -- the total exceptional count is at most 9 C₀ ε n²
  have hE9 : (E:ℝ) ≤ 9*C₀*ε*(n:ℝ)^2 := by
    have h1 := hup o (2*n)
    have hcast : ((2*n : ℕ) : ℝ) = 2*(n:ℝ) := by push_cast; ring
    rw [hcast] at h1
    have h2 : ε * ((P.ball o (2*n)).card : ℝ) ≤ ε * (C₀ * (2*(n:ℝ)+1)^2) :=
      mul_le_mul_of_nonneg_left h1 hε
    have h3 : (2*(n:ℝ)+1)^2 ≤ 9*(n:ℝ)^2 := by nlinarith [hn1R]
    have h4 : ε * (C₀ * (2*(n:ℝ)+1)^2) ≤ ε * (C₀ * (9*(n:ℝ)^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hC₀.le) hε
    have h5 : ε * (C₀ * (9*(n:ℝ)^2)) = 9*C₀*ε*(n:ℝ)^2 := by ring
    linarith [hcount, h2, h4, h5.le, h5.ge]
  by_cases hcase : (E:ℝ) ≤ (n:ℝ)
  · have hbd := le_of_few_exceptional P hc o n 1 f hharm' (by rw [← hE]; exact hcase) x hx
    refine le_trans hbd ?_
    have hpos : (0:ℝ) ≤ A * Real.sqrt ε * (n:ℝ) := by positivity
    calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (A * Real.sqrt ε * (n:ℝ)) := Real.exp_le_exp.mpr hpos
  · push Not at hcase
    have hcaseR : (n:ℝ) < (E:ℝ) := hcase
    -- a lower bound on √ε n
    have hbig : 1/(3*Real.sqrt C₀) ≤ Real.sqrt ε * (n:ℝ) := by
      have h1 : (n:ℝ) < 9*C₀*ε*(n:ℝ)^2 := lt_of_lt_of_le hcaseR hE9
      have h2 : 1/(9*C₀) < ε * (n:ℝ)^2 := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [h1, hn1R, hC₀]
      have h3 : (Real.sqrt ε * (n:ℝ))^2 = ε * (n:ℝ)^2 := by
        rw [mul_pow, Real.sq_sqrt hε]
      have h4 : (1/(3*Real.sqrt C₀))^2 = 1/(9*C₀) := by
        rw [div_pow, mul_pow, Real.sq_sqrt hC₀.le]
        norm_num
      have h5 : (1/(3*Real.sqrt C₀))^2 < (Real.sqrt ε * (n:ℝ))^2 := by rw [h3, h4]; exact h2
      have h6 : (0:ℝ) ≤ Real.sqrt ε * (n:ℝ) := by positivity
      nlinarith [h5, h6, (by positivity : (0:ℝ) < 1/(3*Real.sqrt C₀))]
    -- choose the radius
    set m : ℕ := ⌈δ * Real.sqrt ε * (n:ℝ)⌉₊ with hm
    set r : ℕ := max r₀ m with hr
    have hrr₀ : r₀ ≤ r := le_max_left _ _
    have hmR : (m:ℝ) ≤ δ * Real.sqrt ε * (n:ℝ) + 1 := by
      have := Nat.ceil_lt_add_one (a := δ * Real.sqrt ε * (n:ℝ)) (by positivity)
      linarith
    have hmge : δ * Real.sqrt ε * (n:ℝ) ≤ (m:ℝ) := Nat.le_ceil _
    have hεsmall : Real.sqrt ε ≤ 1/(4*δ) := by
      have h1 : ε ≤ 1/(16*δ^2) := le_of_lt hεlt
      have h2 : Real.sqrt ε ≤ Real.sqrt (1/(16*δ^2)) := Real.sqrt_le_sqrt h1
      have h3 : Real.sqrt (1/(16*δ^2)) = 1/(4*δ) := by
        rw [show (1/(16*δ^2) : ℝ) = (1/(4*δ))^2 by field_simp; ring]
        exact Real.sqrt_sq (by positivity)
      linarith [h2, h3.le, h3.ge]
    have h2m : 2*m ≤ n := by
      have h1 : (2:ℝ)*(m:ℝ) ≤ 2*(δ * Real.sqrt ε * (n:ℝ) + 1) := by linarith
      have h2 : δ * Real.sqrt ε * (n:ℝ) ≤ (n:ℝ)/4 := by
        have h4 : δ * Real.sqrt ε ≤ 1/4 := by
          have h0 := mul_le_mul_of_nonneg_left hεsmall (le_of_lt hδ0)
          calc δ * Real.sqrt ε ≤ δ * (1/(4*δ)) := h0
            _ = 1/4 := by field_simp
        nlinarith [h4, hn1R]
      have h3 : (4:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn4
      have h5 : (2:ℝ)*(m:ℝ) ≤ (n:ℝ) := by linarith
      exact_mod_cast h5
    have h2r : 2*r ≤ n := by
      rw [hr]
      rcases le_total r₀ m with h | h
      · rw [max_eq_right h]; exact h2m
      · rw [max_eq_left h]; exact hnr₀
    have hrge : δ * Real.sqrt ε * (n:ℝ) ≤ (r:ℝ) := by
      refine le_trans hmge ?_
      exact_mod_cast Nat.cast_le.mpr (le_max_right r₀ m)
    have hrle : (r:ℝ) ≤ (r₀:ℝ) + (δ * Real.sqrt ε * (n:ℝ) + 1) := by
      have h1 : r ≤ r₀ + m := max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
      have h2 : (r:ℝ) ≤ (r₀:ℝ) + (m:ℝ) := by exact_mod_cast h1
      linarith
    -- the smaller ball sits inside the big one
    have hballsub : ∀ z ∈ P.ball x (2*r), z ∈ P.ball o (2*n) := by
      intro z hz
      rw [mem_ball_iff] at hz ⊢
      have hxo : P.graph.edist x o ≤ (n : ℕ∞) := (mem_ball_iff P o x n).mp hx
      refine le_trans (SimpleGraph.edist_triangle (v := x)) ?_
      refine le_trans (add_le_add hz hxo) ?_
      rw [← Nat.cast_add]
      exact_mod_cast Nat.cast_le.mpr (by omega : 2*r + n ≤ 2*n)
    have hharmx : LatticeProb.Network.HarmonicOn P.graph c f
        (LatticeProb.Graph.closedBall P.graph x (2*r)) := by
      intro z hz
      refine hharm' z ?_
      have hz' : z ∈ P.ball x (2*r) := by
        have : z ∈ (P.ball x (2*r) : Set V) := by rw [coe_ball]; exact hz
        exact_mod_cast this
      exact hballsub z hz'
    have hcountx : (UCPlanar.exceptionalCount (P.ball x (2*r)) f 1 : ℝ)
        ≤ ε₁ * (P.ball x (2*r)).card := by
      have hmono : UCPlanar.exceptionalCount (P.ball x (2*r)) f 1 ≤ E := by
        rw [hE, UCPlanar.exceptionalCount, UCPlanar.exceptionalCount]
        exact Finset.card_le_card (Finset.filter_subset_filter _ (fun z hz => hballsub z hz))
      have hmonoR : (UCPlanar.exceptionalCount (P.ball x (2*r)) f 1 : ℝ) ≤ (E:ℝ) := by
        exact_mod_cast hmono
      have hlowx := hlow x (2*r)
      have hcast : ((2*r : ℕ) : ℝ) = 2*(r:ℝ) := by push_cast; ring
      rw [hcast] at hlowx
      have hr0R : (0:ℝ) ≤ (r:ℝ) := Nat.cast_nonneg r
      have hstep : 9*C₀*ε*(n:ℝ)^2 ≤ ε₁ * (c₀ * (2*(r:ℝ)+1)^2) := by
        have hq : δ^2 * (ε * (n:ℝ)^2) ≤ (r:ℝ)^2 := by
          have h1 : (δ * Real.sqrt ε * (n:ℝ))^2 = δ^2 * (ε * (n:ℝ)^2) := by
            rw [mul_pow, mul_pow, Real.sq_sqrt hε]; ring
          have h0 : (0:ℝ) ≤ δ * Real.sqrt ε * (n:ℝ) := by positivity
          have h2 : (δ * Real.sqrt ε * (n:ℝ))^2 ≤ (r:ℝ)^2 := by nlinarith only [h0, hrge]
          rw [h1] at h2
          exact h2
        have h2 : 9*C₀*ε*(n:ℝ)^2 ≤ 4*ε₁*c₀*(r:ℝ)^2 := by
          have h3 : 4*ε₁*c₀*(δ^2 * (ε * (n:ℝ)^2)) ≤ 4*ε₁*c₀*(r:ℝ)^2 :=
            mul_le_mul_of_nonneg_left hq (by positivity)
          have h4 : 4*ε₁*c₀*(δ^2 * (ε * (n:ℝ)^2)) = 9*C₀*ε*(n:ℝ)^2 := by
            rw [hδsq]; field_simp
          linarith only [h3, h4.le, h4.ge]
        have h5 : 4*(r:ℝ)^2 ≤ (2*(r:ℝ)+1)^2 := by nlinarith only [hr0R]
        have h6 : ε₁*(c₀*(4*(r:ℝ)^2)) ≤ ε₁*(c₀*(2*(r:ℝ)+1)^2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 hc₀.le) hε₁.le
        have h7 : ε₁*(c₀*(4*(r:ℝ)^2)) = 4*ε₁*c₀*(r:ℝ)^2 := by ring
        linarith only [h2, h6, h7.le, h7.ge]
      have hfin : ε₁ * (c₀ * (2*(r:ℝ)+1)^2) ≤ ε₁ * ((P.ball x (2*r)).card : ℝ) :=
        mul_le_mul_of_nonneg_left hlowx hε₁.le
      linarith only [hmonoR, hE9, hstep, hfin]
    have hxr : x ∈ P.ball x r := by
      rw [mem_ball_iff]
      simp
    have hbd := coarse lam hlam c hc hell x r hrr₀ f hharmx hcountx x hxr
    refine le_trans hbd ?_
    refine Real.exp_le_exp.mpr ?_
    have hbigA : a*((r₀:ℝ)+1) ≤ 3*a*((r₀:ℝ)+1)*Real.sqrt C₀ * (Real.sqrt ε * (n:ℝ)) := by
      have hk : (0:ℝ) ≤ 3*a*((r₀:ℝ)+1)*Real.sqrt C₀ := by positivity
      have h1 := mul_le_mul_of_nonneg_left hbig hk
      have h2 : 3*a*((r₀:ℝ)+1)*Real.sqrt C₀ * (1/(3*Real.sqrt C₀)) = a*((r₀:ℝ)+1) := by
        field_simp
      linarith only [h1, h2.le, h2.ge]
    have hlin : a * (r:ℝ) ≤ a*δ*(Real.sqrt ε * (n:ℝ)) + a*((r₀:ℝ)+1) := by
      have h1 := mul_le_mul_of_nonneg_left hrle ha.le
      have h2 : a*((r₀:ℝ) + (δ * Real.sqrt ε * (n:ℝ) + 1))
          = a*δ*(Real.sqrt ε*(n:ℝ)) + a*((r₀:ℝ)+1) := by ring
      linarith only [h1, h2.le, h2.ge]
    have hid : (a*δ + 3*a*((r₀:ℝ)+1)*Real.sqrt C₀) * Real.sqrt ε * (n:ℝ)
        = a*δ*(Real.sqrt ε * (n:ℝ)) + 3*a*((r₀:ℝ)+1)*Real.sqrt C₀ * (Real.sqrt ε * (n:ℝ)) := by
      ring
    rw [hA, hid]
    linarith only [hlin, hbigA]

end UCPlanar.Support
