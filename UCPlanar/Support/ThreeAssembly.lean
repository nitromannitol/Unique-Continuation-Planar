/-
The three-ball proposition from the lattice inequality: the arithmetic of the degree bound, the
supremum norm on the outer square, and the bound along one coset of the period lattice.
-/
import UCPlanar.Support.ThreeCover
import UCPlanar.Frozen.PolynomialApproximation

open scoped BigOperators Classical
set_option autoImplicit false

namespace UCPlanar.Support.Three

open UCPlanar.Support

/-- A pointwise bound gives a bound on the finite supremum norm. -/
theorem supNorm_le {V : Type*} (S : Finset V) (f : V → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ x ∈ S, |f x| ≤ M) : UCPlanar.supNorm S f ≤ M := by
  rw [UCPlanar.supNorm, ← Real.coe_toNNReal M hM, NNReal.coe_le_coe]
  refine Finset.sup_le (fun x hx => ?_)
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal M hM, coe_nnnorm, Real.norm_eq_abs]
  exact h x hx

/-- The line data is monotone in the error. -/
theorem polyReach_mono (J N m : ℕ) (g : ℤ → ℝ) (ε ε' : ℝ) (hεε : ε ≤ ε')
    (h : PolyReach J N m g ε) : PolyReach J N m g ε' := by
  obtain ⟨q, hdeg, hq⟩ := h
  exact ⟨q, hdeg, fun s hs => le_trans (hq s hs) hεε⟩

/-- The first arithmetic side condition of the propagation. -/
theorem arith_H1 (J n : ℕ) (hJ : 1 ≤ J) (hn : 6 ≤ n) : (3*J+2)*n ≤ 24*J*(n/2) := by
  have hd : n ≤ 2*(n/2) + 1 := by omega
  have h2 : 6 ≤ 2*(n/2) + 1 := by omega
  nlinarith [Nat.zero_le (n/2), Nat.zero_le J]

/-- The second arithmetic side condition of the propagation. -/
theorem arith_H2 (J n : ℕ) (_hJ : 1 ≤ J) : 5*J*(n/2) + 2*n ≤ (3*J+2)*n := by
  have hd : 2*(n/2) ≤ n := by omega
  nlinarith [Nat.zero_le (n/2), Nat.zero_le J, Nat.zero_le n]

/-- A power of two as an exponential. -/
theorem two_pow_eq_exp (n : ℕ) : (2:ℝ)^n = Real.exp (Real.log 2 * n) := by
  rw [← Real.rpow_natCast (2:ℝ) n, Real.rpow_def_of_pos (by norm_num)]

/-- **The three-ball inequality along one coset of the period lattice.** -/
theorem threeBall_orbit {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (hRemez : RemezInput) (J n : ℕ) (hJ : 1 ≤ J) (hn : 6 ≤ n)
    (v : V) (f : V → ℝ) (M ρ B δ R : ℝ) (hM : 1 ≤ M) (hρ : 0 ≤ ρ) (hB0 : 0 ≤ B)
    (hB : ∀ u : UCPlanar.Plane, ‖P.period u‖ ≤ B * ‖u‖) (hv : ‖P.pos v‖ ≤ ρ)
    (hfit : ρ + B * (2^J*(n:ℝ)) ≤ δ * R)
    (happ : ∀ m : ℕ, 2*m ≤ n → P.PolynomialApproximation R m v f (alphaJ J) δ)
    (hsup : UCPlanar.supNorm (P.square (3*R)) f ≤ M)
    (hbound : ∀ s t : ℤ, |s| ≤ 2^J*(n:ℤ) → |t| ≤ 2^J*(n:ℤ) → |orbLine P f v s t| ≤ M)
    (hdens : (1 - (1/4:ℝ)) * (((box n).card : ℕ) : ℝ) ≤
      ((((box n).filter (fun x => |orbLine P f v x.1 x.2| ≤ 1)).card : ℕ) : ℝ)) :
    ∀ s t : ℤ, |s| ≤ 2^J*(n:ℤ) → |t| ≤ 2^J*(n:ℤ) →
      |orbLine P f v s t| ≤ 2*(CJ J)^2 * M^(1/2:ℝ) + (6*CJ J+3)*M/2^n := by
  have hmono : ∀ m : ℕ, (alphaJ J) ^ m * UCPlanar.supNorm (P.square (3*R)) f
      ≤ (alphaJ J) ^ m * M := by
    intro m
    have := alphaJ_pos J
    exact mul_le_mul_of_nonneg_left hsup (by positivity)
  refine threeBall_reach hRemez J n hn hJ (arith_H1 J n hJ hn) (arith_H2 J n hJ)
    (orbLine P f v) M (1/4) hM (le_refl _) hbound ?_ ?_ hdens
  · intro m hm t ht
    exact polyReach_mono J n m _ _ _ (hmono m)
      (polyReach_horizontal_of_fit P R m J n v f (alphaJ J) δ ρ B hB0 hρ hB hv hfit
        (happ m hm) t ht)
  · intro m hm s hs
    exact polyReach_mono J n m _ _ _ (hmono m)
      (polyReach_vertical_of_fit P R m J n v f (alphaJ J) δ ρ B hB0 hρ hB hv hfit
        (happ m hm) s hs)

set_option maxHeartbeats 4000000 in
/-- **The main case of the three-ball proposition**: the scale is above the threshold fixed by
the geometry and the outer bound is above one.  The point is carried to the lattice box of one
coset, where the reach-`2^J` inequality applies. -/
theorem threeBall_main {V : Type*} (P : UCPlanar.PeriodicGraph V) (hRemez : RemezInput)
    (B K C₀ ρ ε : ℝ) (hB1 : 1 ≤ B) (hK1 : 1 ≤ K) (hC₀0 : 0 < C₀) (hρ0 : 0 ≤ ρ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1/(16*B^2*C₀))
    (hB : ∀ u : UCPlanar.Plane, ‖P.period u‖ ≤ B * ‖u‖)
    (hKb : ∀ (a : Fin 2 → ℤ) (Mv : ℝ), 0 ≤ Mv →
      ‖P.period (fun j => (a j : ℝ))‖ ≤ Mv → ∀ j, |(a j : ℝ)| ≤ K * Mv)
    (hC₀ : ∀ R : ℝ, 1 ≤ R → ((P.square R).card : ℝ) ≤ C₀ * R ^ 2)
    (hρv : ∀ v ∈ P.representatives, ‖P.pos v‖ ≤ ρ)
    (J : ℕ) (hJ1 : 1 ≤ J) (hJreach : 12*K*B ≤ (2:ℝ)^J) (_hpow2 : (2:ℝ) ≤ (2:ℝ)^J)
    (c : V → V → ℝ) (δ R₀ : ℝ) (hδ : 0 < δ) (hR₀ : 0 < R₀)
    (happrox : ∀ R : ℝ, R₀ ≤ R → ∀ m : ℕ, (m : ℝ) ≤ δ*R → ∀ (v : V) (f : V → ℝ),
      LatticeProb.Network.HarmonicOn P.graph c f (P.square (3*R) : Set V) →
      P.PolynomialApproximation R m v f (alphaJ J) δ)
    (c₀ : ℝ) (hc₀le : c₀ ≤ Real.log 2/(8*B))
    (N₀ : ℕ) (hN₀ : 14*B + 2*ρ ≤ (N₀:ℝ))
    (k : ℕ) (hk : 3*ρ/δ + 3*B*(2:ℝ)^J/δ + 3*R₀ + ρ + B*(2:ℝ)^J + 4 ≤ (k:ℝ))
    (C : ℝ) (hCa : 2*(CJ J)^2 ≤ C) (hCb : 6*CJ J+3 ≤ C)
    (N : ℕ) (f : V → ℝ) (M : ℝ)
    (hharm : LatticeProb.Network.HarmonicOn P.graph c f (P.square (k*N) : Set V))
    (hdens : 1 - ε ≤ UCPlanar.boundedDensity (P.square N) f 1)
    (hMbound : ∀ x ∈ P.square (k*N), |f x| ≤ M)
    (x : V) (hx : x ∈ P.square (2*N)) (hMbig : 1 < M) (hNbig : N₀ ≤ N) :
    |f x| ≤ C*Real.sqrt M + C*Real.exp (-c₀*N)*M := by
  classical
  have hBpos : (0:ℝ) < B := by linarith
  have hM0 : (0:ℝ) ≤ M := by linarith
  have hNbigR : (N₀:ℝ) ≤ (N:ℝ) := by exact_mod_cast hNbig
  have hNge : 14*B + 2*ρ ≤ (N:ℝ) := le_trans hN₀ hNbigR
  have hBne : (B:ℝ) ≠ 0 := ne_of_gt hBpos
  have hNR : (1:ℝ) ≤ (N:ℝ) := by linarith
  have hN : 0 < N := by
    by_contra hcon
    have : N = 0 := by omega
    rw [this] at hNR
    norm_num at hNR
  -- the lattice radius of the density box
  obtain ⟨n, hndef⟩ : ∃ n : ℕ, n = ⌊(N:ℝ)/(2*B)⌋₊ := ⟨_, rfl⟩
  have hnle : (n:ℝ) ≤ (N:ℝ)/(2*B) := by rw [hndef]; exact Nat.floor_le (by positivity)
  have hngt : (N:ℝ)/(2*B) - 1 < (n:ℝ) := by
    have h := Nat.lt_floor_add_one ((N:ℝ)/(2*B))
    rw [hndef]
    linarith
  have hquart : (1:ℝ) ≤ (N:ℝ)/(4*B) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hhalfsum : (N:ℝ)/(4*B) + (N:ℝ)/(4*B) = (N:ℝ)/(2*B) := by field_simp; ring
  have hnquarter : (N:ℝ)/(4*B) ≤ (n:ℝ) := by linarith
  have hn6 : 6 ≤ n := by
    have h1 : (7:ℝ) ≤ (N:ℝ)/(2*B) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have h2 : (6:ℝ) < (n:ℝ) := by linarith
    have h3 : ((6:ℕ):ℝ) < (n:ℝ) := by push_cast; linarith
    have := (Nat.cast_lt (α := ℝ)).mp h3
    omega
  have hnN : (n:ℝ) ≤ (N:ℝ) := by
    have : (N:ℝ)/(2*B) ≤ (N:ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hNR, hB1]
    linarith
  have hhalfB : B*((N:ℝ)/(2*B)) = (N:ℝ)/2 := by field_simp
  have hBn : B*(n:ℝ) ≤ (N:ℝ)/2 := by
    have h := mul_le_mul_of_nonneg_left hnle hBpos.le
    rw [hhalfB] at h
    exact h
  have hfit0 : ρ + B*(n:ℝ) ≤ (N:ℝ) := by linarith
  -- the coset of x
  obtain ⟨v, hv, a, hav⟩ := P.covers x
  have hvρ : ‖P.pos v‖ ≤ ρ := hρv v hv
  have hxorb : orbPt P v (a 0, a 1) = x := by
    show P.shift ((a 0) • UCPlanar.Support.e₁ + (a 1) • UCPlanar.Support.e₂) v = x
    rw [← UCPlanar.Support.site_eq_smul a]
    exact hav
  have hposx : ‖P.pos x‖ ≤ 2*(N:ℝ) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr ?_
    intro i
    simpa [Real.norm_eq_abs] using (UCPlanar.Support.mem_square_iff P (2*N) x).mp hx i
  have hperiod : P.period (fun j => (a j : ℝ)) = P.pos x - P.pos v := by
    have h := P.pos_shift a v
    rw [hav] at h
    linear_combination (norm := abel) -h
  have hnorm : ‖P.period (fun j => (a j : ℝ))‖ ≤ 2*(N:ℝ) + ρ := by
    rw [hperiod]
    have h3 : ‖P.pos x - P.pos v‖ ≤ ‖P.pos x‖ + ‖P.pos v‖ := norm_sub_le _ _
    linarith
  have haj : ∀ j, |(a j : ℝ)| ≤ K*(2*(N:ℝ)+ρ) :=
    hKb a (2*(N:ℝ)+ρ) (by positivity) hnorm
  have hreach : ∀ j, |(a j : ℝ)| ≤ (2:ℝ)^J*(n:ℝ) := by
    intro j
    have hρN : ρ ≤ (N:ℝ) := by linarith
    have h1 : K*(2*(N:ℝ)+ρ) ≤ 3*K*(N:ℝ) := by nlinarith [hK1, hρN]
    have h2 : 3*K*(N:ℝ) ≤ (2:ℝ)^J*(n:ℝ) := by
      have h4 : (0:ℝ) ≤ (N:ℝ)/(4*B) := by positivity
      have h3 : 12*K*B*((N:ℝ)/(4*B)) ≤ (2:ℝ)^J*(n:ℝ) := by
        calc 12*K*B*((N:ℝ)/(4*B)) ≤ (2:ℝ)^J*((N:ℝ)/(4*B)) :=
              mul_le_mul_of_nonneg_right hJreach h4
          _ ≤ (2:ℝ)^J*(n:ℝ) := mul_le_mul_of_nonneg_left hnquarter (by positivity)
      have h5 : 12*K*B*((N:ℝ)/(4*B)) = 3*K*(N:ℝ) := by
        field_simp
        ring
      linarith
    linarith [haj j]
  have hcastZ : ∀ j, |a j| ≤ 2^J*(n:ℤ) := by
    intro j
    have h := hreach j
    rw [← Int.cast_abs] at h
    have h2 : ((|a j| : ℤ) : ℝ) ≤ ((2^J*(n:ℤ) : ℤ) : ℝ) := by push_cast at h ⊢; linarith
    exact_mod_cast h2
  -- the scale of the polynomial approximation
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = (ρ + B*(2:ℝ)^J*(N:ℝ))/δ + R₀ := ⟨_, rfl⟩
  have hpowpos : (0:ℝ) < (2:ℝ)^J := by positivity
  have hRR₀ : R₀ ≤ R := by
    have : (0:ℝ) ≤ (ρ + B*(2:ℝ)^J*(N:ℝ))/δ := by positivity
    linarith
  have hδR : δ*R = ρ + B*(2:ℝ)^J*(N:ℝ) + δ*R₀ := by
    rw [hRdef]; field_simp
  have hδR₀ : (0:ℝ) < δ*R₀ := by positivity
  have hBJ : (2:ℝ) ≤ B*(2:ℝ)^J := by nlinarith [hB1, _hpow2]
  have hfitJ : ρ + B*((2:ℝ)^J*(n:ℝ)) ≤ δ*R := by
    rw [hδR]
    have h2 : B*((2:ℝ)^J*(n:ℝ)) = B*(2:ℝ)^J*(n:ℝ) := by ring
    have h1 : B*(2:ℝ)^J*(n:ℝ) ≤ B*(2:ℝ)^J*(N:ℝ) :=
      mul_le_mul_of_nonneg_left hnN (by positivity)
    rw [h2]
    linarith
  have hbig : 2*(N:ℝ) ≤ δ*R := by
    rw [hδR]
    have h1 : 2*(N:ℝ) ≤ B*(2:ℝ)^J*(N:ℝ) :=
      mul_le_mul_of_nonneg_right hBJ (by positivity)
    linarith
  have hA1 : (0:ℝ) ≤ 3*ρ/δ := by positivity
  have hA2 : (0:ℝ) ≤ 3*B*(2:ℝ)^J/δ := by positivity
  have hA3 : (0:ℝ) ≤ 3*R₀ := by linarith
  have hkk : 3*ρ/δ + 3*B*(2:ℝ)^J/δ + 3*R₀ ≤ (k:ℝ) := by
    have h : (0:ℝ) ≤ ρ + B*(2:ℝ)^J + 4 := by positivity
    linarith
  have hkk2 : ρ + B*(2:ℝ)^J ≤ (k:ℝ) := by linarith
  have h3R : 3*R ≤ (k:ℝ)*(N:ℝ) := by
    have hR' : 3*R = 3*ρ/δ + (3*B*(2:ℝ)^J/δ)*(N:ℝ) + 3*R₀ := by
      rw [hRdef]; field_simp
    have e1 : 3*ρ/δ ≤ (3*ρ/δ)*(N:ℝ) := by
      nlinarith [mul_nonneg hA1 (sub_nonneg.mpr hNR)]
    have e3 : 3*R₀ ≤ (3*R₀)*(N:ℝ) := by
      nlinarith [mul_nonneg hA3 (sub_nonneg.mpr hNR)]
    have e4 : (3*ρ/δ)*(N:ℝ) + (3*B*(2:ℝ)^J/δ)*(N:ℝ) + (3*R₀)*(N:ℝ) ≤ (k:ℝ)*(N:ℝ) := by
      have h := mul_le_mul_of_nonneg_right hkk (by positivity : (0:ℝ) ≤ (N:ℝ))
      calc (3*ρ/δ)*(N:ℝ) + (3*B*(2:ℝ)^J/δ)*(N:ℝ) + (3*R₀)*(N:ℝ)
          = (3*ρ/δ + 3*B*(2:ℝ)^J/δ + 3*R₀)*(N:ℝ) := by ring
        _ ≤ (k:ℝ)*(N:ℝ) := h
    linarith
  have hfitk : ρ + B*((2:ℝ)^J*(n:ℝ)) ≤ (k:ℝ)*(N:ℝ) := by
    have h1 : B*((2:ℝ)^J*(n:ℝ)) = B*(2:ℝ)^J*(n:ℝ) := by ring
    have h2 : B*(2:ℝ)^J*(n:ℝ) ≤ B*(2:ℝ)^J*(N:ℝ) :=
      mul_le_mul_of_nonneg_left hnN (by positivity)
    have h3 : ρ + B*(2:ℝ)^J*(N:ℝ) ≤ (ρ + B*(2:ℝ)^J)*(N:ℝ) := by
      nlinarith [mul_nonneg hρ0 (sub_nonneg.mpr hNR)]
    have h4 : (ρ + B*(2:ℝ)^J)*(N:ℝ) ≤ (k:ℝ)*(N:ℝ) :=
      mul_le_mul_of_nonneg_right hkk2 (by positivity)
    rw [h1]
    linarith
  have hsub3 : P.square (3*R) ⊆ P.square (k*N) := UCPlanar.Support.square_mono P (by linarith)
  have hharm3 : LatticeProb.Network.HarmonicOn P.graph c f (P.square (3*R) : Set V) :=
    fun y hy => hharm y (Finset.coe_subset.mpr hsub3 hy)
  have happm : ∀ m : ℕ, 2*m ≤ n → P.PolynomialApproximation R m v f (alphaJ J) δ := by
    intro m hm
    refine happrox R hRR₀ m ?_ v f hharm3
    have h1 : (m:ℝ) ≤ (n:ℝ) := by
      have : m ≤ n := by omega
      exact_mod_cast this
    linarith
  have hsup : UCPlanar.supNorm (P.square (3*R)) f ≤ M :=
    supNorm_le _ _ M hM0 (fun y hy => hMbound y (hsub3 hy))
  have hbound : ∀ s' t' : ℤ, |s'| ≤ 2^J*(n:ℤ) → |t'| ≤ 2^J*(n:ℤ) →
      |orbLine P f v s' t'| ≤ M := by
    intro s' t' hs' ht'
    exact hMbound _ (orbit_mem_square P v s' t' ρ B ((2:ℝ)^J*(n:ℝ)) (by linarith) (by positivity)
      hρ0 hB hvρ (reach_cast J n s' hs') (reach_cast J n t' ht') ((k:ℝ)*(N:ℝ)) hfitk)
  -- the density of the coset box
  have hmaps : ∀ y ∈ box n, orbPt P v y ∈ P.square N := by
    intro y hy
    rw [box, show (seg n).product (seg n) = seg n ×ˢ seg n from rfl, Finset.mem_product] at hy
    simp only [seg, Finset.mem_Icc] at hy
    obtain ⟨⟨ha1, ha2⟩, hb1, hb2⟩ := hy
    have h1 : |(y.1 : ℝ)| ≤ (n:ℝ) := by
      rw [← Int.cast_abs]
      have h : |y.1| ≤ (n:ℤ) := by rw [abs_le]; exact ⟨ha1, ha2⟩
      exact_mod_cast h
    have h2 : |(y.2 : ℝ)| ≤ (n:ℝ) := by
      rw [← Int.cast_abs]
      have h : |y.2| ≤ (n:ℤ) := by rw [abs_le]; exact ⟨hb1, hb2⟩
      exact_mod_cast h
    exact orbit_mem_square P v y.1 y.2 ρ B (n:ℝ) (by linarith) (by positivity) hρ0 hB hvρ h1 h2
      (N:ℝ) hfit0
  have hcount : ε * (((P.square (N:ℝ)).card : ℕ) : ℝ) ≤ (1/4) * (((box n).card : ℕ) : ℝ) := by
    have h1 : (((P.square (N:ℝ)).card : ℕ) : ℝ) ≤ C₀*(N:ℝ)^2 := hC₀ (N:ℝ) hNR
    have h2 : (((box n).card : ℕ) : ℝ) = (2*(n:ℝ)+1)^2 := by
      rw [box_card]; push_cast; ring
    have h3 : (N:ℝ)^2/(16*B^2) ≤ (1/4)*(2*(n:ℝ)+1)^2 := by
      have h5 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      have hX0 : (0:ℝ) ≤ (N:ℝ)/(4*B) := by positivity
      have h6 : ((N:ℝ)/(4*B))^2 = (N:ℝ)^2/(16*B^2) := by
        rw [div_pow]
        congr 1
        ring
      have h7 : ((N:ℝ)/(4*B))^2 ≤ (n:ℝ)^2 := pow_le_pow_left₀ hX0 hnquarter 2
      have h8 : (n:ℝ)^2 ≤ (1/4)*(2*(n:ℝ)+1)^2 := by nlinarith [h5]
      rw [← h6]
      linarith
    have h7 : ε * (((P.square (N:ℝ)).card : ℕ) : ℝ) ≤ ε * (C₀*(N:ℝ)^2) :=
      mul_le_mul_of_nonneg_left h1 hε0
    have h8 : ε * (C₀*(N:ℝ)^2) ≤ (N:ℝ)^2/(16*B^2) := by
      have h9 : ε * (C₀*(N:ℝ)^2) ≤ (1/(16*B^2*C₀)) * (C₀*(N:ℝ)^2) :=
        mul_le_mul_of_nonneg_right hε (by positivity)
      have h10 : (1/(16*B^2*C₀)) * (C₀*(N:ℝ)^2) = (N:ℝ)^2/(16*B^2) := by
        field_simp
      linarith
    rw [h2]
    calc ε * (((P.square (N:ℝ)).card : ℕ) : ℝ) ≤ ε * (C₀*(N:ℝ)^2) := h7
      _ ≤ (N:ℝ)^2/(16*B^2) := h8
      _ ≤ (1/4)*(2*(n:ℝ)+1)^2 := h3
  have hdens' := coset_density P f v n (N:ℝ) ε hε0 hmaps hdens hcount
  -- the lattice inequality along the coset
  have hmain := threeBall_orbit P hRemez J n hJ1 hn6 v f M ρ B δ R (le_of_lt hMbig) hρ0
    (by linarith) hB hvρ hfitJ happm hsup hbound hdens' (a 0) (a 1) (hcastZ 0) (hcastZ 1)
  have hfxeq : orbLine P f v (a 0) (a 1) = f x := by
    rw [← hxorb]
    rfl
  rw [hfxeq] at hmain
  -- the two terms of the conclusion
  have hsq : M ^ (1/2:ℝ) = Real.sqrt M := (Real.sqrt_eq_rpow M).symm
  have hterm1 : 2*(CJ J)^2 * M^(1/2:ℝ) ≤ C * Real.sqrt M := by
    rw [hsq]
    exact mul_le_mul_of_nonneg_right hCa (Real.sqrt_nonneg M)
  have hexp : (1:ℝ)/2^n ≤ Real.exp (-c₀*(N:ℝ)) := by
    have hpn : (2:ℝ)^n = Real.exp (Real.log 2 * n) := two_pow_eq_exp n
    have hle : c₀*(N:ℝ) ≤ Real.log 2 * (n:ℝ) := by
      have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have h1 : c₀*(N:ℝ) ≤ (Real.log 2/(8*B))*(N:ℝ) :=
        mul_le_mul_of_nonneg_right hc₀le (by positivity)
      have h2 : (Real.log 2/(8*B))*(N:ℝ) ≤ Real.log 2 * ((N:ℝ)/(4*B)) := by
        have he : (Real.log 2/(8*B))*(N:ℝ) = (Real.log 2*(N:ℝ))/(8*B) := by ring
        have he2 : Real.log 2 * ((N:ℝ)/(4*B)) = (Real.log 2*(N:ℝ))/(4*B) := by ring
        have hX : (0:ℝ) ≤ Real.log 2*(N:ℝ) := by positivity
        rw [he, he2, div_le_div_iff₀ (by positivity) (by positivity)]
        exact mul_le_mul_of_nonneg_left (by linarith only [hBpos]) hX
      have h3 : Real.log 2 * ((N:ℝ)/(4*B)) ≤ Real.log 2 * (n:ℝ) :=
        mul_le_mul_of_nonneg_left hnquarter hlog2.le
      linarith only [h1, h2, h3]
    rw [hpn, one_div, ← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by linarith only [hle])
  have hterm2 : (6*CJ J+3)*M/2^n ≤ C * Real.exp (-c₀*(N:ℝ)) * M := by
    have hpos : (0:ℝ) < (2:ℝ)^n := by positivity
    have h1 : (6*CJ J+3)*M/2^n = (6*CJ J+3) * ((1:ℝ)/2^n) * M := by
      rw [one_div, div_eq_mul_inv]
      ring
    rw [h1]
    have h2 : (6*CJ J+3) * ((1:ℝ)/2^n) ≤ C * Real.exp (-c₀*(N:ℝ)) := by
      have h3 : (0:ℝ) ≤ (1:ℝ)/2^n := by positivity
      have h4 : (0:ℝ) < 6*CJ J+3 := by linarith only [CJ_ge_three J]
      calc (6*CJ J+3) * ((1:ℝ)/2^n) ≤ (6*CJ J+3) * Real.exp (-c₀*(N:ℝ)) :=
            mul_le_mul_of_nonneg_left hexp h4.le
        _ ≤ C * Real.exp (-c₀*(N:ℝ)) :=
            mul_le_mul_of_nonneg_right hCb (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_right h2 hM0
  linarith only [hmain, hterm1, hterm2]

set_option maxHeartbeats 1000000 in
/-- **The three-ball proposition.**  The lattice inequality along every coset of the period
lattice, the covering of the geometric square by the finitely many cosets, and the choice of the
outer radius from the scale of the polynomial approximation. -/
theorem threeBall_assembled {V : Type*} (P : UCPlanar.PeriodicGraph V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ c : V → V → ℝ,
      LatticeProb.Network.IsCond P.graph c → P.PeriodicConductance c →
      UCPlanar.External.MoserEstimate P c →
      ∃ (k : ℕ) (c₀ C : ℝ), 4 ≤ k ∧ 0 < c₀ ∧ 0 < C ∧
      ∀ N : ℕ, 0 < N → ∀ (f : V → ℝ) (M : ℝ), 0 ≤ M →
        LatticeProb.Network.HarmonicOn P.graph c f (P.square (k*N) : Set V) →
        1 - ε ≤ UCPlanar.boundedDensity (P.square N) f 1 →
        (∀ x ∈ P.square (k*N), |f x| ≤ M) →
        ∀ x ∈ P.square (2*N), |f x| ≤ C*Real.sqrt M + C*Real.exp (-c₀*N)*M := by
  classical
  have hRemez : RemezInput := remezInput
  obtain ⟨B₀, hB₀0, hB₀⟩ := UCPlanar.Support.exists_period_bound P
  obtain ⟨K₀, hK₀0, hK₀⟩ := UCPlanar.Support.exists_lattice_count P.period
  obtain ⟨C₀, hC₀0, hC₀⟩ := UCPlanar.Support.exists_square_card_bound P
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = B₀ + 1 := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = K₀ + 1 := ⟨_, rfl⟩
  have hB1 : (1:ℝ) ≤ B := by rw [hBdef]; linarith
  have hK1 : (1:ℝ) ≤ K := by rw [hKdef]; linarith
  have hB : ∀ u : UCPlanar.Plane, ‖P.period u‖ ≤ B * ‖u‖ := by
    intro u
    have h := hB₀ u
    have : B₀ * ‖u‖ ≤ B * ‖u‖ := by
      rw [hBdef]
      nlinarith [norm_nonneg u]
    linarith
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = ∑ v ∈ P.representatives, ‖P.pos v‖ := ⟨_, rfl⟩
  have hρ0 : (0:ℝ) ≤ ρ := by
    rw [hρdef]; exact Finset.sum_nonneg (fun v _ => norm_nonneg _)
  have hρv : ∀ v ∈ P.representatives, ‖P.pos v‖ ≤ ρ := by
    intro v hv
    rw [hρdef]
    exact Finset.single_le_sum (f := fun v => ‖P.pos v‖) (fun v _ => norm_nonneg _) hv
  refine ⟨1/(16*B^2*C₀), by positivity, ?_⟩
  intro c hc hp hMos
  obtain ⟨J, hJdef⟩ : ∃ J : ℕ, J = max 1 ⌈12*K*B⌉₊ := ⟨_, rfl⟩
  have hJ1 : 1 ≤ J := by rw [hJdef]; exact le_max_left _ _
  have hJreach : 12*K*B ≤ (2:ℝ)^J := by
    have h1 : (12*K*B : ℝ) ≤ (⌈12*K*B⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈12*K*B⌉₊ : ℕ) ≤ J := by rw [hJdef]; exact le_max_right _ _
    have h3 : ((⌈12*K*B⌉₊ : ℕ) : ℝ) ≤ (J : ℝ) := by exact_mod_cast h2
    have h4 : (J : ℝ) ≤ (2:ℝ)^J := by
      have := Nat.lt_two_pow_self (n := J)
      have h5 : (J : ℝ) < ((2^J : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h5
      linarith
    linarith
  have hpow2 : (2:ℝ) ≤ (2:ℝ)^J := by
    calc (2:ℝ) = (2:ℝ)^(1:ℕ) := by norm_num
      _ ≤ (2:ℝ)^J := pow_le_pow_right₀ (by norm_num) hJ1
  obtain ⟨δ, R₀, hδ, hR₀, happrox⟩ :=
    UCPlanar.Frozen.polynomialApproximation P c hc hp hMos (alphaJ J) (alphaJ_pos J)
  obtain ⟨c₀, hc₀def⟩ : ∃ c₀ : ℝ, c₀ = Real.log 2/(8*B) := ⟨_, rfl⟩
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hc₀ : 0 < c₀ := by rw [hc₀def]; positivity
  obtain ⟨N₀, hN₀def⟩ : ∃ N₀ : ℕ, N₀ = ⌈14*B + 2*ρ⌉₊ + 1 := ⟨_, rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ, k = ⌈3*ρ/δ + 3*B*(2:ℝ)^J/δ + 3*R₀ + ρ + B*(2:ℝ)^J⌉₊ + 4 := ⟨_, rfl⟩
  have hk4 : 4 ≤ k := by rw [hkdef]; omega
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max (max (2*(CJ J)^2) (6*CJ J+3)) (Real.exp (c₀*N₀)) := ⟨_, rfl⟩
  have hCa : 2*(CJ J)^2 ≤ C := by rw [hCdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hCb : 6*CJ J+3 ≤ C := by rw [hCdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hCc : Real.exp (c₀*N₀) ≤ C := by rw [hCdef]; exact le_max_right _ _
  have hC1 : (1:ℝ) ≤ C := by
    have := CJ_ge_three J
    nlinarith [hCa]
  have hC0 : 0 < C := by linarith
  refine ⟨k, c₀, C, hk4, hc₀, hC0, ?_⟩
  intro N hN f M hM0 hharm hdens hMbound x hx
  have hNR : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hkN : (2*N : ℝ) ≤ (k*N : ℝ) := by
    have : (4:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk4
    nlinarith
  have hxk : x ∈ P.square (k*N) := UCPlanar.Support.square_mono P hkN hx
  have hfx : |f x| ≤ M := hMbound x hxk
  have hdecaynn : (0:ℝ) ≤ C*Real.exp (-c₀*N)*M := by positivity
  have hsqrtnn : (0:ℝ) ≤ C*Real.sqrt M := by positivity
  rcases le_or_gt M 1 with hMsmall | hMbig
  · -- a bound below one is already below its own square root
    have hs2 : (0:ℝ) ≤ Real.sqrt M := Real.sqrt_nonneg M
    have hle : M ≤ Real.sqrt M := by
      have hs1 : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM0
      nlinarith [hs1, hs2, hMsmall, hM0]
    have hCs : Real.sqrt M ≤ C * Real.sqrt M := by
      have h := mul_le_mul_of_nonneg_right hC1 hs2
      rwa [one_mul] at h
    linarith only [hfx, hle, hCs, hdecaynn]
  · rcases lt_or_ge N N₀ with hNsmall | hNbig
    · -- the small scales are absorbed by the constant
      have h1 : (N:ℝ) ≤ (N₀:ℝ) := by exact_mod_cast le_of_lt hNsmall
      have h2 : Real.exp (c₀*N) ≤ Real.exp (c₀*N₀) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h1 hc₀.le)
      have h3 : (1:ℝ) ≤ C * Real.exp (-c₀*N) := by
        have h4 : Real.exp (c₀*(N:ℝ)) * Real.exp (-c₀*(N:ℝ)) = 1 := by
          rw [← Real.exp_add, show c₀*(N:ℝ) + -c₀*(N:ℝ) = 0 by ring, Real.exp_zero]
        have h5 : (0:ℝ) < Real.exp (-c₀*(N:ℝ)) := Real.exp_pos _
        calc (1:ℝ) = Real.exp (c₀*(N:ℝ)) * Real.exp (-c₀*(N:ℝ)) := h4.symm
          _ ≤ Real.exp (c₀*(N₀:ℝ)) * Real.exp (-c₀*(N:ℝ)) :=
              mul_le_mul_of_nonneg_right h2 h5.le
          _ ≤ C * Real.exp (-c₀*(N:ℝ)) := mul_le_mul_of_nonneg_right hCc h5.le
      have hge : M ≤ C * Real.exp (-c₀*N) * M := by nlinarith [h3, hM0]
      linarith only [hfx, hge, hsqrtnn]
    · have hKb : ∀ (a : Fin 2 → ℤ) (Mv : ℝ), 0 ≤ Mv →
          ‖P.period (fun j => (a j : ℝ))‖ ≤ Mv → ∀ j, |(a j : ℝ)| ≤ K * Mv := by
        intro a Mv hMv hnorm j
        have h := hK₀ a Mv hnorm j
        have hKK : K₀ ≤ K := by rw [hKdef]; linarith
        have h2 : K₀*Mv ≤ K*Mv := mul_le_mul_of_nonneg_right hKK hMv
        linarith
      have hN₀le : 14*B + 2*ρ ≤ (N₀:ℝ) := by
        rw [hN₀def]
        have := Nat.le_ceil (14*B + 2*ρ)
        push_cast
        linarith
      have hkle : 3*ρ/δ + 3*B*(2:ℝ)^J/δ + 3*R₀ + ρ + B*(2:ℝ)^J + 4 ≤ (k:ℝ) := by
        rw [hkdef]
        have := Nat.le_ceil (3*ρ/δ + 3*B*(2:ℝ)^J/δ + 3*R₀ + ρ + B*(2:ℝ)^J)
        push_cast
        linarith
      exact threeBall_main P hRemez B K C₀ ρ (1/(16*B^2*C₀)) hB1 hK1 hC₀0 hρ0
        (by positivity) (le_refl _) hB hKb hC₀ hρv J hJ1 hJreach hpow2 c δ R₀ hδ hR₀
        happrox c₀ (le_of_eq hc₀def) N₀ hN₀le k hkle C hCa hCb N f M hharm hdens hMbound
        x hx hMbig hNbig

end UCPlanar.Support.Three
