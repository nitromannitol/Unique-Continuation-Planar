/-
The bounded-value density passes from the metric balls to the geometric squares.

A geometric square of radius `K` lies in a metric ball of radius at most `Cg K + c₂`, that ball
lies in a geometric square of radius linear in `K`, and both squares have cardinality comparable
with `K²`.  So a density at least `1 - ε` on the balls gives a density at least `1 - C ε` on the
squares at every large radius, with `C` a constant of the graph.
-/
import UCPlanar.Basic
import UCPlanar.Support.ZeroVolume
import UCPlanar.Support.Poly.Square
import UCPlanar.Support.Poly.Volume
import UCPlanar.Support.LowerVolume
import UCPlanar.Support.LiouCount
import UCPlanar.Support.LiouEventually
import UCPlanar.Support.LiouFinalGeom
import UCPlanar.Support.ZeroAssemble

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace UCPlanar.Support

theorem ball_subset_square_linear {V : Type*} (P : UCPlanar.PeriodicGraph V) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (o : V) (n : ℕ), P.ball o n ⊆ P.square (‖P.pos o‖ + D * n) := by
  obtain ⟨D, hD0, hD⟩ := UCPlanar.Support.exists_edge_bound P
  refine ⟨D, hD0, ?_⟩
  intro o n x hx
  obtain ⟨p, hp⟩ := UCPlanar.Support.exists_short_walk P o n hx
  have h1 : ‖P.pos x - P.pos o‖ ≤ D * p.length := UCPlanar.Support.norm_pos_sub_le_walk P D hD p
  have h2 : (p.length : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp
  have h3 : ‖P.pos x - P.pos o‖ ≤ D * n := le_trans h1 (mul_le_mul_of_nonneg_left h2 hD0)
  rw [UCPlanar.Support.mem_square_iff]
  intro i
  have h4 : |P.pos x i - P.pos o i| ≤ ‖P.pos x - P.pos o‖ := by
    have h := norm_le_pi_norm (P.pos x - P.pos o) i
    rw [Real.norm_eq_abs] at h
    simpa using h
  have h5 : |P.pos o i| ≤ ‖P.pos o‖ := by
    have h := norm_le_pi_norm (P.pos o) i
    rwa [Real.norm_eq_abs] at h
  have h6 : |P.pos x i| - |P.pos o i| ≤ |P.pos x i - P.pos o i| :=
    abs_sub_abs_le_abs_sub _ _
  linarith

theorem density_ge_of_exceptionalCount {V : Type*} (S : Finset V) (f : V → ℝ) (t : ℝ)
    (hcard : 0 < S.card) (h : (UCPlanar.exceptionalCount S f 1 : ℝ) ≤ t * S.card) :
    1 - t ≤ UCPlanar.boundedDensity S f 1 := by
  have hSpos : (0:ℝ) < (S.card : ℝ) := by exact_mod_cast hcard
  have hsplit : ((S.filter (fun x => |f x| ≤ 1)).card : ℝ)
      + ((S.filter (fun x => ¬ (|f x| ≤ 1))).card : ℝ) = (S.card : ℝ) := by
    have h' := Finset.card_filter_add_card_filter_not (s := S) (p := fun x => |f x| ≤ 1)
    exact_mod_cast h'
  have hexc : UCPlanar.exceptionalCount S f 1 = (S.filter (fun x => ¬ (|f x| ≤ 1))).card := by
    rw [UCPlanar.exceptionalCount]
    congr 1
    apply Finset.filter_congr
    intro x _
    simp [not_le]
  rw [hexc] at h
  rw [UCPlanar.boundedDensity, le_div_iff₀ hSpos]
  linarith

/-- **The bounded-value density transfers from the metric balls to the geometric squares.**
The square of radius `K` sits in a ball whose radius is at most `Cg K + c₂`, that ball sits in a
square of radius linear in `K`, and the two squares have comparable quadratic cardinalities, so
the exceptional vertices of the square are a bounded multiple of the fraction they occupy in the
ball.  The multiple depends only on the graph. -/
theorem exists_density_transfer {V : Type*} (P : UCPlanar.PeriodicGraph V) :
    ∃ Ctr : ℝ, 0 < Ctr ∧ ∀ (o : V) (f : V → ℝ) (ε : ℝ), 0 < ε →
      P.HasBoundedDensity o f ε →
      ∀ᶠ N : ℕ in Filter.atTop, ∀ K : ℕ, Real.sqrt N ≤ K → K ≤ 2*N →
        1 - Ctr*ε ≤ UCPlanar.boundedDensity (P.square K) f 1 := by
  classical
  obtain ⟨D, hD0, hDsq⟩ := ball_subset_square_linear P
  obtain ⟨Cup, hCup0, hCup⟩ := UCPlanar.Support.exists_square_card_bound P
  obtain ⟨κ, hκ0, R₁, hR₁0, hκ⟩ := UCPlanar.Support.Lower.exists_square_card_lower P
  obtain ⟨Cg, hCg0, hgeo⟩ := UCPlanar.Support.LiouFinal.exists_square_ball_uniform P
  set a : ℝ := (D + 1) * Cg with hadef
  have ha0 : 0 < a := by rw [hadef]; positivity
  refine ⟨2 * Cup * (a + 1) ^ 2 / κ, by positivity, ?_⟩
  set Ctr : ℝ := 2 * Cup * (a + 1) ^ 2 / κ with hCtrdef
  intro o f ε hε hdens
  obtain ⟨m₁, hm₁⟩ := Filter.eventually_atTop.mp
    (UCPlanar.Support.eventually_density_ge P o f ε ε hε hdens)
  obtain ⟨c₂, hc₂0, hgeoN⟩ := hgeo o
  set γ : ℝ := ‖P.pos o‖ + D * c₂ with hγdef
  have hγ0 : 0 ≤ γ := by rw [hγdef]; positivity
  set T : ℝ := max (max γ 1) (max R₁ ((m₁ : ℝ) / Cg)) with hTdef
  have hT0 : 0 ≤ T := le_trans (le_trans zero_le_one (le_max_right γ 1)) (le_max_left _ _)
  refine Filter.eventually_atTop.mpr ⟨⌈T ^ 2⌉₊, ?_⟩
  intro N hN K hK _
  -- every admissible `K` is beyond the threshold
  have hTK : T ≤ (K : ℝ) := by
    have h1 : T ^ 2 ≤ (N : ℝ) := by
      have h2 : (⌈T ^ 2⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      exact le_trans (Nat.le_ceil _) h2
    have h3 : Real.sqrt (T ^ 2) ≤ Real.sqrt N := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq hT0] at h3
    exact le_trans h3 hK
  have hKγ : γ ≤ (K : ℝ) := le_trans (le_trans (le_max_left γ 1) (le_max_left _ _)) hTK
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := le_trans (le_trans (le_max_right γ 1) (le_max_left _ _)) hTK
  have hKR₁ : R₁ ≤ (K : ℝ) := le_trans (le_trans (le_max_left R₁ _) (le_max_right _ _)) hTK
  have hKm : (m₁ : ℝ) ≤ Cg * (K : ℝ) := by
    have h1 : (m₁ : ℝ) / Cg ≤ (K : ℝ) :=
      le_trans (le_trans (le_max_right R₁ _) (le_max_right _ _)) hTK
    rw [div_le_iff₀ hCg0] at h1
    linarith
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := le_trans zero_le_one hK1
  -- the square is large
  have hsqlow : κ * (K : ℝ) ^ 2 ≤ ((P.square (K : ℝ)).card : ℝ) := hκ (K : ℝ) hKR₁
  have hsqpos : 0 < (P.square (K : ℝ)).card := by
    have h1 : (0 : ℝ) < κ * (K : ℝ) ^ 2 := by positivity
    have h2 : (0 : ℝ) < ((P.square (K : ℝ)).card : ℝ) := lt_of_lt_of_le h1 hsqlow
    exact_mod_cast h2
  -- a ball containing it
  obtain ⟨n, hnle, hsub⟩ := hgeoN (K : ℝ) hK0
  set nn : ℕ := max n m₁ with hnndef
  have hnnle : (nn : ℝ) ≤ Cg * (K : ℝ) + c₂ := by
    rw [hnndef, Nat.cast_max]
    exact max_le hnle (by linarith)
  have hnnm : m₁ ≤ nn := le_max_right n m₁
  have hsubnn : P.square (K : ℝ) ⊆ P.ball o nn := by
    intro x hx
    have h1 : x ∈ P.ball o n := by
      have := hsub (by exact hx : x ∈ (P.square (K : ℝ) : Set V))
      exact this
    rw [UCPlanar.Support.mem_ball_iff_dist] at h1 ⊢
    exact le_trans h1 (by exact_mod_cast le_max_left n m₁)
  -- the ball is small
  have hballpos : 0 < (P.ball o nn).card := by
    refine Finset.card_pos.mpr ⟨o, ?_⟩
    rw [UCPlanar.Support.mem_ball_iff_dist]
    simp
  have hRb : ‖P.pos o‖ + D * (nn : ℝ) ≤ (a + 1) * (K : ℝ) := by
    have h1 : D * (nn : ℝ) ≤ D * (Cg * (K : ℝ) + c₂) := mul_le_mul_of_nonneg_left hnnle hD0
    have h2 : D * Cg ≤ a := by rw [hadef]; nlinarith
    nlinarith
  have hballsub : P.ball o nn ⊆ P.square ((a + 1) * (K : ℝ)) :=
    fun x hx => UCPlanar.Support.square_mono P hRb (hDsq o nn hx)
  have hballcard : ((P.ball o nn).card : ℝ) ≤ Cup * ((a + 1) * (K : ℝ)) ^ 2 := by
    have h1 : ((P.ball o nn).card : ℝ) ≤ ((P.square ((a + 1) * (K : ℝ))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hballsub
    have h2 : (1 : ℝ) ≤ (a + 1) * (K : ℝ) := by nlinarith
    exact le_trans h1 (hCup _ h2)
  -- the exceptional count of the ball
  have hdb : 1 - (2 * ε) ≤ UCPlanar.boundedDensity (P.ball o nn) f 1 := by
    have := hm₁ nn hnnm
    linarith
  have hexcball : (UCPlanar.exceptionalCount (P.ball o nn) f 1 : ℝ)
      ≤ (2 * ε) * ((P.ball o nn).card : ℝ) :=
    UCPlanar.Support.exceptionalCount_le_of_density _ f (2 * ε) hballpos hdb
  -- transfer to the square
  have hexcsq : (UCPlanar.exceptionalCount (P.square (K : ℝ)) f 1 : ℝ)
      ≤ (UCPlanar.exceptionalCount (P.ball o nn) f 1 : ℝ) := by
    exact_mod_cast UCPlanar.Support.exceptionalCount_le_of_subset hsubnn f 1
  have hchain : (UCPlanar.exceptionalCount (P.square (K : ℝ)) f 1 : ℝ)
      ≤ Ctr * ε * ((P.square (K : ℝ)).card : ℝ) := by
    have h1 : (2 * ε) * ((P.ball o nn).card : ℝ)
        ≤ (2 * ε) * (Cup * ((a + 1) * (K : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left hballcard (by positivity)
    have h2 : Ctr * ε * (κ * (K : ℝ) ^ 2) = (2 * ε) * (Cup * ((a + 1) * (K : ℝ)) ^ 2) := by
      rw [hCtrdef]; field_simp
    have h3 : Ctr * ε * (κ * (K : ℝ) ^ 2) ≤ Ctr * ε * ((P.square (K : ℝ)).card : ℝ) :=
      mul_le_mul_of_nonneg_left hsqlow (by rw [hCtrdef]; positivity)
    linarith
  exact density_ge_of_exceptionalCount _ f (Ctr * ε) hsqpos hchain

end UCPlanar.Support
