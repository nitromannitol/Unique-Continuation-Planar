/-
The assembly of the exponential lower bound.

The chain dichotomy of `prop22` is run along the dyadic ladder `K_i = 2^i K₀` with
`K₀ ≍ √N`, the inner scale of each rung is `L_i = ⌊K_i / (13(k+1))⌋`, the density hypothesis is
transferred from the square of radius `2K_i` to every small square centred at a lattice point
inside it, and the bootstrap supplies the constant that starts the chain.  The ladder has
`l ≍ log₂ √N` rungs, so the squaring branch produces `2^{32^l}` with `32^l ≥ N`, and the
exponential branch produces `exp(c₁ 2^{l-1} K₀)` with `2^{l-1} K₀ ≥ N/4`.
-/
import UCPlanar.Support.LowerBootstrap
import UCPlanar.Support.LowerLadder
import UCPlanar.Support.LowerChain

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace UCPlanar.Support.Lower

/-- A square of radius at least the covering radius of the vertex orbits is nonempty. -/
theorem square_nonempty {V : Type*} (P : UCPlanar.PeriodicGraph V) (ρ : ℝ)
    (hcentre : ∀ x : V, ∃ a : LatticeProb.Site 2, x ∈ squareAt P a ρ) (R : ℝ) (hR : ρ ≤ R) :
    (P.square R).Nonempty := by
  obtain ⟨x⟩ := P.connected.nonempty
  obtain ⟨a, ha⟩ := hcentre x
  exact ⟨P.shift (-a) x,
    UCPlanar.Support.square_mono P hR ((mem_squareAt P a ρ x).mp ha)⟩


/-- **The exponential lower bound on a periodic graph.**  The dyadic ladder of the chain
dichotomy, started at the scale `E⌊√N⌋` by the bootstrap and run to the scale `N`. -/
theorem periodicLowerBound_main {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (c : V → V → ℝ) (hc : LatticeProb.Network.IsCond P.graph c)
    (hp : P.PeriodicConductance c)
    (hMos : UCPlanar.External.MoserEstimate P c) :
    ∃ b : ℝ, 0 < b ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ N : ℕ, N₀ ≤ N → ∀ f : V → ℝ,
        LatticeProb.Network.HarmonicOn P.graph c f Set.univ →
        (∃ x ∈ P.square (Nat.sqrt N), 2 ≤ f x) →
        (∀ K : ℕ, Real.sqrt N ≤ K → K ≤ 2*N →
          1 - ε ≤ UCPlanar.boundedDensity (P.square K) f 1) →
        Real.exp (b*N) ≤ UCPlanar.supNorm (P.square N) f := by
  classical
  obtain ⟨ρ, hρ0, hcentre⟩ := exists_centre P
  obtain ⟨κ, hκ0, R₁, hR₁0, hκ⟩ := exists_square_card_lower P
  obtain ⟨Cup, hCup0, hCup⟩ := UCPlanar.Support.exists_square_card_bound P
  obtain ⟨εtb, hεtb0, hbody⟩ := threeBall_shift P
  obtain ⟨k, c₀, C, hk4, hc₀, hC, htb⟩ := hbody c hc hp hMos
  obtain ⟨ε₁, hε₁0, hboot⟩ := bootstrap P c hc hp hMos
  set C₁ : ℝ := max ((2*C)^4) 2 with hC₁def
  obtain ⟨A, hA0, N₁, hN₁0, hbootA⟩ := hboot C₁
  set D : ℕ := 13*(k+1) with hDdef
  have hD0 : 0 < D := by rw [hDdef]; omega
  have hDR0 : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD0
  have hDne : ((D:ℕ):ℝ) ≠ 0 := ne_of_gt hDR0
  set c₁ : ℝ := c₀/(4*(D:ℝ)) with hc₁def
  have hc₁0 : 0 < c₁ := by rw [hc₁def]; positivity
  set Lmin : ℕ := ⌈max (max ρ R₁) (2*Real.log (2*C)/c₀)⌉₊ + 1 with hLmindef
  set G : ℕ := 2*D*(Lmin+2) with hGdef
  set E : ℕ := 2*⌈A⌉₊ + 2 + G with hEdef
  set b : ℝ := min (Real.log 2) (c₁/4) with hbdef
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hb0 : 0 < b := by rw [hbdef]; exact lt_min hlog2 (by positivity)
  have hE1 : 1 ≤ E := by rw [hEdef]; omega
  refine ⟨b, hb0, min ε₁ (εtb*κ/(16*Cup*(D:ℝ)^2)), lt_min hε₁0 (by positivity),
    max N₁ (32*E^5), lt_of_lt_of_le hN₁0 (le_max_left _ _), ?_⟩
  intro ε hε0 hεlt N hN f hharm hx₀ hdens
  have hεε₁ : ε < ε₁ := lt_of_lt_of_le hεlt (min_le_left _ _)
  have hεε₂ : ε * (16*Cup*(D:ℝ)^2) < εtb*κ := by
    have := lt_of_lt_of_le hεlt (min_le_right _ _)
    rwa [lt_div_iff₀ (by positivity)] at this
  have hNN₁ : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hNE : 32*E^5 ≤ N := le_trans (le_max_right _ _) hN
  -- the base of the ladder
  set s : ℕ := Nat.sqrt N with hsdef
  have hE2s : 2*E ≤ s := by
    rw [hsdef, Nat.le_sqrt]
    have hpow : E^2 ≤ E^5 := Nat.pow_le_pow_right hE1 (by norm_num)
    calc 2*E*(2*E) = 4*E^2 := by ring
      _ ≤ 32*E^2 := Nat.mul_le_mul_right _ (by norm_num)
      _ ≤ 32*E^5 := Nat.mul_le_mul_left _ hpow
      _ ≤ N := hNE
  have hEs : E ≤ s := by omega
  have hs2 : 2 ≤ s := by omega
  have hs0 : 0 < s := by omega
  have hssm : s * s ≤ N := by
    have h := Nat.sqrt_le' N
    rw [pow_two] at h
    rw [hsdef]; exact h
  have hsN : s ≤ N := by rw [hsdef]; exact Nat.sqrt_le_self N
  have hsR0 : (0:ℝ) < (s:ℝ) := by exact_mod_cast hs0
  have hsR1 : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs0
  have hsle : (s:ℝ) ≤ Real.sqrt N := by
    have h1 : ((s*s : ℕ):ℝ) ≤ ((N:ℕ):ℝ) := by exact_mod_cast hssm
    have h2 : (s:ℝ)^2 ≤ ((N:ℕ):ℝ) := by push_cast at h1; nlinarith [h1]
    nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ ((N:ℕ):ℝ)),
      Real.sqrt_nonneg ((N:ℕ):ℝ), hsR0]
  have hNlt : Real.sqrt N ≤ 2*(s:ℝ) := by
    have h1 : N < (s+1)^2 := by rw [hsdef]; exact Nat.lt_succ_sqrt' N
    have h2 : ((N:ℕ):ℝ) ≤ ((s:ℝ)+1)^2 := by
      have h3 : ((N:ℕ):ℝ) ≤ (((s+1)^2 : ℕ):ℝ) := by exact_mod_cast h1.le
      push_cast at h3 ⊢; nlinarith [h3]
    nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ ((N:ℕ):ℝ)),
      Real.sqrt_nonneg ((N:ℕ):ℝ), hsR1]
  set K₀n : ℕ := E * s with hK₀ndef
  have hK₀n0 : 0 < K₀n := by rw [hK₀ndef]; positivity
  have hK₀nN : K₀n ≤ N := by
    calc K₀n = E*s := hK₀ndef
      _ ≤ s*s := Nat.mul_le_mul_right s hEs
      _ ≤ N := hssm
  have hK₀nR0 : (0:ℝ) < (K₀n:ℝ) := by exact_mod_cast hK₀n0
  have hsK₀n : s ≤ K₀n := by
    calc s ≤ E*s := Nat.le_mul_of_pos_left _ (by omega)
      _ = K₀n := hK₀ndef.symm
  have hK₀A : A * Real.sqrt N ≤ (K₀n:ℝ) := by
    have hAE : 2*A ≤ ((2*⌈A⌉₊ : ℕ):ℝ) := by
      have := Nat.le_ceil A
      push_cast
      linarith
    have h1 : ((2*⌈A⌉₊ : ℕ):ℝ) ≤ (E:ℝ) := by
      have h5 : (2*⌈A⌉₊ : ℕ) ≤ E := by rw [hEdef]; omega
      exact_mod_cast h5
    have h2 : A * Real.sqrt N ≤ A * (2*(s:ℝ)) :=
      mul_le_mul_of_nonneg_left hNlt hA0.le
    have h3 : A * (2*(s:ℝ)) ≤ (E:ℝ) * (s:ℝ) := by nlinarith [hsR0, hAE, h1]
    have h4 : (K₀n:ℝ) = (E:ℝ)*(s:ℝ) := by rw [hK₀ndef]; push_cast; ring
    rw [h4]; linarith
  -- the length of the ladder
  set l : ℕ := Nat.findGreatest (fun m => 2^m * K₀n ≤ N) N with hldef
  have hlspec : 2^l * K₀n ≤ N := by
    rw [hldef]
    exact Nat.findGreatest_spec (P := fun m => 2^m * K₀n ≤ N) (Nat.zero_le N)
      (by simpa using hK₀nN)
  have hlN : l ≤ N := by rw [hldef]; exact Nat.findGreatest_le N
  have hllt : l < N := by
    rcases lt_or_eq_of_le hlN with h | h
    · exact h
    · exfalso
      rw [h] at hlspec
      have h1 : N < 2^N := Nat.lt_two_pow_self
      have h2 : 2^N ≤ 2^N * K₀n := Nat.le_mul_of_pos_right _ hK₀n0
      omega
  have hlgt : N < 2^(l+1) * K₀n := by
    rcases Nat.lt_or_ge N (2^(l+1)*K₀n) with h | h
    · exact h
    · exfalso
      have hle : l + 1 ≤ l := by
        rw [hldef]
        exact Nat.le_findGreatest (by omega) h
      omega
  have hl1 : 1 ≤ l := by
    by_contra hcon
    have hl0 : l = 0 := by omega
    rw [hl0] at hlgt
    have h1 : 2^(0+1) * K₀n = 2*E*s := by rw [hK₀ndef]; ring
    have h2 : 2*E*s ≤ s*s := Nat.mul_le_mul_right s hE2s
    omega
  -- the ladder hypotheses
  have hmono : ∀ r t : ℝ, r ≤ t →
      UCPlanar.supNorm (P.square r) f ≤ UCPlanar.supNorm (P.square t) f := fun r t h =>
    UCPlanar.Support.supNorm_mono (UCPlanar.Support.square_mono P h) f
  have hbootr : ∀ r : ℝ, (K₀n:ℝ) ≤ r → C₁ ≤ UCPlanar.supNorm (P.square r) f := fun r hr =>
    hbootA ε hε0 hεε₁ N hNN₁ f hharm hx₀ hdens r (le_trans hK₀A hr)
  have hC₁2 : (2:ℝ) ≤ C₁ := le_max_right _ _
  have hone : ∀ r : ℝ, (K₀n:ℝ) ≤ r → 1 ≤ UCPlanar.supNorm (P.square r) f := fun r hr => by
    linarith [hbootr r hr, hC₁2]
  have hbootK₀ : 2 ≤ UCPlanar.supNorm (P.square (K₀n:ℝ)) f :=
    le_trans hC₁2 (hbootr _ le_rfl)
  -- one rung of the ladder
  have hstep : ∀ i, i < l →
      min (32 * Real.log (UCPlanar.supNorm (P.square ((2:ℝ)^i*(K₀n:ℝ))) f))
          (Real.log (UCPlanar.supNorm (P.square ((2:ℝ)^i*(K₀n:ℝ))) f)
            + c₁*((2:ℝ)^i*(K₀n:ℝ)))
        ≤ Real.log (UCPlanar.supNorm (P.square ((2:ℝ)^(i+1)*(K₀n:ℝ))) f) := by
    intro i hi
    set Ki : ℕ := 2^i * K₀n with hKidef
    set Li : ℕ := Ki / D with hLidef
    have hKicast : ((Ki:ℕ):ℝ) = (2:ℝ)^i*(K₀n:ℝ) := by rw [hKidef]; push_cast; ring
    have hKi_ge : K₀n ≤ Ki := by
      rw [hKidef]
      exact Nat.le_mul_of_pos_left _ (by positivity)
    have hKi_le : Ki ≤ N := by
      have h1 : (2:ℕ)^i ≤ 2^l := Nat.pow_le_pow_right (by norm_num) hi.le
      calc Ki = 2^i*K₀n := hKidef
        _ ≤ 2^l*K₀n := Nat.mul_le_mul_right _ h1
        _ ≤ N := hlspec
    have hKi1 : 1 ≤ Ki := le_trans hK₀n0 hKi_ge
    have hKiR1 : (1:ℝ) ≤ (Ki:ℝ) := by exact_mod_cast hKi1
    have hKi0 : (0:ℝ) < (Ki:ℝ) := by linarith
    have hGE : G ≤ K₀n := by
      have h1 : G ≤ E := by rw [hEdef]; omega
      calc G ≤ E := h1
        _ ≤ E*s := Nat.le_mul_of_pos_right _ hs0
        _ = K₀n := hK₀ndef.symm
    have hLiLmin : Lmin + 1 ≤ Li := by
      rw [hLidef, Nat.le_div_iff_mul_le hD0]
      calc (Lmin+1)*D ≤ 2*D*(Lmin+2) := by nlinarith [Nat.zero_le D, Nat.zero_le Lmin]
        _ = G := hGdef.symm
        _ ≤ K₀n := hGE
        _ ≤ Ki := hKi_ge
    have hLi0 : 0 < Li := by omega
    have hDLi : D * Li ≤ Ki := by
      rw [hLidef]; exact Nat.mul_div_le Ki D
    have hLiKi : Li ≤ Ki := by rw [hLidef]; exact Nat.div_le_self Ki D
    have hKiLi2 : Ki ≤ 2*D*Li := by
      have hmod : D * Li + Ki % D = Ki := by rw [hLidef]; exact Nat.div_add_mod Ki D
      have hlt : Ki % D < D := Nat.mod_lt _ hD0
      have hDD : D ≤ D*Li := Nat.le_mul_of_pos_right _ hLi0
      calc Ki = D*Li + Ki % D := hmod.symm
        _ ≤ D*Li + D := Nat.add_le_add_left hlt.le _
        _ ≤ D*Li + D*Li := Nat.add_le_add_left hDD _
        _ = 2*D*Li := by ring
    have hKL : (Ki:ℝ) ≤ 2*((D:ℕ):ℝ)*((Li:ℕ):ℝ) := by exact_mod_cast hKiLi2
    -- the inner scale is above all the fixed thresholds
    have hLminR : max (max ρ R₁) (2*Real.log (2*C)/c₀) ≤ ((Lmin:ℕ):ℝ) := by
      have h1 := Nat.le_ceil (max (max ρ R₁) (2*Real.log (2*C)/c₀))
      have h2 : ((⌈max (max ρ R₁) (2*Real.log (2*C)/c₀)⌉₊ : ℕ):ℝ) ≤ ((Lmin:ℕ):ℝ) := by
        have h3 : ⌈max (max ρ R₁) (2*Real.log (2*C)/c₀)⌉₊ ≤ Lmin := by rw [hLmindef]; omega
        exact_mod_cast h3
      linarith
    have hLiR : ((Lmin:ℕ):ℝ) ≤ ((Li:ℕ):ℝ) := by
      have h1 : Lmin ≤ Li := by omega
      exact_mod_cast h1
    have hLiρ : ρ ≤ ((Li:ℕ):ℝ) :=
      le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLminR) hLiR
    have hLiR₁ : R₁ ≤ ((Li:ℕ):ℝ) :=
      le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLminR) hLiR
    have hLilog : 2*Real.log (2*C)/c₀ ≤ ((Li:ℕ):ℝ) :=
      le_trans (le_trans (le_max_right _ _) hLminR) hLiR
    have hLipos : (0:ℝ) < ((Li:ℕ):ℝ) := by exact_mod_cast hLi0
    have hLiCt : 2*C ≤ Real.exp (c₀*((Li:ℕ):ℝ)/2) := by
      have h1 : Real.log (2*C) ≤ c₀*((Li:ℕ):ℝ)/2 := by
        rw [div_le_iff₀ hc₀] at hLilog
        linarith
      calc 2*C = Real.exp (Real.log (2*C)) := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp (c₀*((Li:ℕ):ℝ)/2) := Real.exp_le_exp.mpr h1
    have hρKi : ρ ≤ (Ki:ℝ) := by
      have h1 : ((Li:ℕ):ℝ) ≤ (Ki:ℝ) := by exact_mod_cast hLiKi
      linarith [hLiρ]
    have hfit : 13*(ρ + (k:ℝ)*((Li:ℕ):ℝ)) ≤ (Ki:ℝ) := by
      have h1 : ((D:ℕ):ℝ) * ((Li:ℕ):ℝ) ≤ (Ki:ℝ) := by exact_mod_cast hDLi
      have h2 : ((D:ℕ):ℝ) = 13*((k:ℝ)+1) := by rw [hDdef]; push_cast; ring
      rw [h2] at h1
      nlinarith [hLiρ, h1, Nat.cast_nonneg (α := ℝ) k, hLipos]
    -- the density at every small square centred at a lattice point
    have hdensLoc : ∀ a : LatticeProb.Site 2,
        squareAt P a ((Li:ℕ):ℝ) ⊆ P.square (2*(Ki:ℝ)) →
        1 - εtb ≤ UCPlanar.boundedDensity (squareAt P a ((Li:ℕ):ℝ)) f 1 := by
      intro a hsub
      refine density_squareAt P f a ((Li:ℕ):ℝ) (2*(Ki:ℝ)) ε εtb hsub
        (square_nonempty P ρ hcentre _ hLiρ) ?_ ?_
      · have h1 : Real.sqrt N ≤ (((2*Ki : ℕ)):ℝ) := by
          have h2 : ((2*s : ℕ):ℝ) ≤ ((2*Ki : ℕ):ℝ) := by
            have h3 : 2*s ≤ 2*Ki := by omega
            exact_mod_cast h3
          have h4 : ((2*s : ℕ):ℝ) = 2*(s:ℝ) := by push_cast; ring
          linarith [hNlt, h2, h4]
        have h5 : 2*Ki ≤ 2*N := by omega
        have h6 := hdens (2*Ki) h1 h5
        have heq : (((2*Ki : ℕ)):ℝ) = 2*(Ki:ℝ) := by push_cast; ring
        rwa [heq] at h6
      · have hcard1 : (((P.square (2*(Ki:ℝ))).card : ℕ) : ℝ) ≤ Cup * (2*(Ki:ℝ))^2 :=
          hCup _ (by linarith)
        have hcard2 : κ * ((Li:ℕ):ℝ)^2 ≤ (((P.square ((Li:ℕ):ℝ)).card : ℕ) : ℝ) :=
          hκ _ hLiR₁
        have h0 : (0:ℝ) ≤ 2*(Ki:ℝ) := by linarith
        have h1 : 2*(Ki:ℝ) ≤ 4*((D:ℕ):ℝ)*((Li:ℕ):ℝ) := by linarith [hKL]
        have hms := mul_self_le_mul_self h0 h1
        have hsq : (2*(Ki:ℝ))^2 ≤ 16*((D:ℕ):ℝ)^2*((Li:ℕ):ℝ)^2 := by nlinarith [hms]
        have hA' : ε * (Cup * (2*(Ki:ℝ))^2)
            ≤ ε * (Cup * (16*((D:ℕ):ℝ)^2*((Li:ℕ):ℝ)^2)) := by
          have h2 : Cup * (2*(Ki:ℝ))^2 ≤ Cup * (16*((D:ℕ):ℝ)^2*((Li:ℕ):ℝ)^2) :=
            mul_le_mul_of_nonneg_left hsq hCup0.le
          exact mul_le_mul_of_nonneg_left h2 hε0.le
        have hB' : ε * (Cup * (16*((D:ℕ):ℝ)^2*((Li:ℕ):ℝ)^2))
            = (ε * (16*Cup*((D:ℕ):ℝ)^2)) * ((Li:ℕ):ℝ)^2 := by ring
        have hC' : (ε * (16*Cup*((D:ℕ):ℝ)^2)) * ((Li:ℕ):ℝ)^2
            ≤ (εtb*κ) * ((Li:ℕ):ℝ)^2 :=
          mul_le_mul_of_nonneg_right hεε₂.le (by positivity)
        have hD' : (εtb*κ) * ((Li:ℕ):ℝ)^2 = εtb * (κ * ((Li:ℕ):ℝ)^2) := by ring
        have hfin1 : ε * (((P.square (2*(Ki:ℝ))).card : ℕ) : ℝ)
            ≤ ε * (Cup * (2*(Ki:ℝ))^2) := mul_le_mul_of_nonneg_left hcard1 hε0.le
        have hfin2 : εtb * (κ * ((Li:ℕ):ℝ)^2)
            ≤ εtb * (((P.square ((Li:ℕ):ℝ)).card : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hcard2 hεtb0.le
        linarith
    -- the rung
    have hprop := prop22 P c f ρ hρ0 hcentre k (by omega) c₀ C εtb C₁ hC hc₀ htb hharm
      (le_max_left _ _) (lt_of_lt_of_le (by norm_num) hC₁2)
      Li hLi0 hLiρ hLiCt (Ki:ℝ) hKi0 hfit
      (hbootr _ (by exact_mod_cast hKi_ge)) hdensLoc
      (square_nonempty P ρ hcentre _ hρKi)
    have hgain : c₁*(Ki:ℝ) ≤ c₀*((Li:ℕ):ℝ)/2 := by
      have h1 : c₁*(Ki:ℝ) ≤ c₁*(2*((D:ℕ):ℝ)*((Li:ℕ):ℝ)) :=
        mul_le_mul_of_nonneg_left hKL hc₁0.le
      have h2 : c₁*(2*((D:ℕ):ℝ)*((Li:ℕ):ℝ)) = c₀*((Li:ℕ):ℝ)/2 := by
        rw [hc₁def]; field_simp; ring
      linarith [h1, h2]
    have heq1 : (2:ℝ)^(i+1)*(K₀n:ℝ) = 2*(Ki:ℝ) := by rw [hKicast]; ring
    rw [← hKicast, heq1]
    refine le_trans (min_le_min le_rfl ?_) hprop
    linarith [hgain]
  -- the top of the ladder
  have htop : (2:ℝ)^l * (K₀n:ℝ) ≤ (N:ℝ) := by exact_mod_cast hlspec
  have hNpow : N ≤ 32^l := by
    have h2 : N^5 < (2*2^l*K₀n)^5 := by
      have h3 : N < 2*2^l*K₀n := by
        have h4 : (2:ℕ)^(l+1) = 2*2^l := by rw [pow_succ]; ring
        calc N < 2^(l+1)*K₀n := hlgt
          _ = 2*2^l*K₀n := by rw [h4]
      exact Nat.pow_lt_pow_left h3 (by norm_num)
    have h3 : (2*2^l*K₀n)^5 = (2^l)^5*(32*K₀n^5) := by ring
    have hs5 : s^5 ≤ N^3 := by
      calc s^5 = (s*s)*((s*s)*s) := by ring
        _ ≤ N*(N*N) := Nat.mul_le_mul hssm (Nat.mul_le_mul hssm hsN)
        _ = N^3 := by ring
    have h4 : 32*K₀n^5 ≤ N^4 := by
      calc 32*K₀n^5 = 32*E^5*s^5 := by rw [hK₀ndef]; ring
        _ ≤ 32*E^5*N^3 := Nat.mul_le_mul (le_refl _) hs5
        _ ≤ N*N^3 := Nat.mul_le_mul hNE (le_refl _)
        _ = N^4 := by ring
    have h5 : N*(32*K₀n^5) ≤ N^5 := by
      calc N*(32*K₀n^5) ≤ N*N^4 := Nat.mul_le_mul (le_refl _) h4
        _ = N^5 := by ring
    have h6 : N*(32*K₀n^5) < (2^l)^5*(32*K₀n^5) := by
      rw [h3] at h2; exact lt_of_le_of_lt h5 h2
    have h7 : N < (2^l)^5 := lt_of_mul_lt_mul_right h6 (Nat.zero_le _)
    have h8 : ((2:ℕ)^l)^5 = 32^l := by
      rw [← pow_mul, show (32:ℕ) = 2^5 by norm_num, ← pow_mul, Nat.mul_comm]
    omega
  have hb1 : b * (N:ℝ) ≤ Real.log 2 * 32^l := by
    have h1 : b ≤ Real.log 2 := min_le_left _ _
    have h2 : ((N:ℕ):ℝ) ≤ ((32^l : ℕ):ℝ) := by exact_mod_cast hNpow
    have h3 : ((32^l : ℕ):ℝ) = (32:ℝ)^l := by push_cast; ring
    rw [h3] at h2
    calc b*(N:ℝ) ≤ Real.log 2 * (N:ℝ) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ Real.log 2 * (32:ℝ)^l := mul_le_mul_of_nonneg_left h2 hlog2.le
  have hb2 : b * (N:ℝ) ≤ c₁ * ((2:ℝ)^(l-1)*(K₀n:ℝ)) := by
    have hpow : (2:ℝ)^(l+1) = 4*(2:ℝ)^(l-1) := by
      have h1 : l - 1 + 2 = l + 1 := by omega
      rw [← h1, pow_add]; ring
    have h2 : ((N:ℕ):ℝ) < ((2^(l+1)*K₀n : ℕ):ℝ) := by exact_mod_cast hlgt
    have h3 : ((2^(l+1)*K₀n : ℕ):ℝ) = (2:ℝ)^(l+1)*(K₀n:ℝ) := by push_cast; ring
    rw [h3, hpow] at h2
    have h4 : b ≤ c₁/4 := min_le_right _ _
    calc b*(N:ℝ) ≤ (c₁/4)*(N:ℝ) := mul_le_mul_of_nonneg_right h4 (by positivity)
      _ ≤ (c₁/4)*(4*(2:ℝ)^(l-1)*(K₀n:ℝ)) :=
          mul_le_mul_of_nonneg_left h2.le (by positivity)
      _ = c₁*((2:ℝ)^(l-1)*(K₀n:ℝ)) := by ring
  exact theoremB_abstract (fun r => UCPlanar.supNorm (P.square r) f) c₁ b (K₀n:ℝ) N l
    hK₀nR0 hc₁0 hmono hone hbootK₀ hstep htop hb1 hb2

end UCPlanar.Support.Lower
