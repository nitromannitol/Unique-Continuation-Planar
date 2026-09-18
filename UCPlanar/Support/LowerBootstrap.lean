/-
The bootstrap constant of the exponential lower bound.

The chain of three-ball inequalities only gains once the maximum exceeds a fixed constant.  That
constant comes from the gradient estimate, not from the three-ball inequality: if the maximum over
a square whose radius is a large multiple of `√N` were bounded by a constant, then every lattice
increment inside the orbit box of half-side `⌊√N⌋` would be below `1/(8⌊√N⌋)`, the value `2` would
propagate to the whole orbit box, and the orbit box would be an exceptional set too large for the
density hypothesis at that scale.
-/
import UCPlanar.Support.LowerBoot

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace UCPlanar.Support.Lower

/-- **The bootstrap.**  For every constant `C₁` there are a multiplier `A` and a threshold `N₁`
such that a harmonic function which reaches `2` on `Q_{⌊√N⌋}` and is at most `1` on a
`(1-ε)`-fraction of every square of radius between `√N` and `2N` has maximum at least `C₁` on
every square of radius at least `A √N`.  The smallness threshold for `ε` depends only on the
network. -/
theorem bootstrap {V : Type*} (P : UCPlanar.PeriodicGraph V) (c : V → V → ℝ)
    (hc : LatticeProb.Network.IsCond P.graph c) (hp : P.PeriodicConductance c)
    (hMos : UCPlanar.External.MoserEstimate P c) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ C₁ : ℝ, ∃ A : ℝ, 0 < A ∧ ∃ N₁ : ℕ, 0 < N₁ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ N : ℕ, N₁ ≤ N → ∀ f : V → ℝ,
        LatticeProb.Network.HarmonicOn P.graph c f Set.univ →
        (∃ x ∈ P.square (Nat.sqrt N), 2 ≤ f x) →
        (∀ K : ℕ, Real.sqrt N ≤ K → K ≤ 2*N →
          1 - ε ≤ UCPlanar.boundedDensity (P.square K) f 1) →
        ∀ r : ℝ, A * Real.sqrt N ≤ r → C₁ ≤ UCPlanar.supNorm (P.square r) f := by
  classical
  obtain ⟨B, hB0, hB⟩ := UCPlanar.Support.exists_period_bound P
  obtain ⟨Cup, hCup0, hCup⟩ := UCPlanar.Support.exists_square_card_bound P
  obtain ⟨Cg, hCg0, hCg⟩ := single_step_bound P c hc hp hMos (vec 1 0) (vec 0 1)
  set b₁ : ℕ := ⌈B⌉₊ + 2 with hb₁def
  have hb₁2 : 2 ≤ b₁ := by omega
  have hb₁R : (2:ℝ) ≤ (b₁:ℝ) := by exact_mod_cast hb₁2
  have hBb₁ : B ≤ (b₁:ℝ) - 2 := by
    have h := Nat.le_ceil B
    have : ((b₁:ℕ):ℝ) = ((⌈B⌉₊ : ℕ):ℝ) + 2 := by rw [hb₁def]; push_cast; ring
    rw [this]; linarith
  refine ⟨4/(Cup * (b₁:ℝ)^2), by positivity, ?_⟩
  intro C₁
  set C₁' : ℝ := max C₁ 1 with hC₁'def
  have hC₁'1 : (1:ℝ) ≤ C₁' := le_max_right _ _
  set A : ℝ := max (3*(b₁:ℝ)) (max (3*Cg + 3) (24*Cg*C₁')) with hAdef
  have hA1 : 3*(b₁:ℝ) ≤ A := le_max_left _ _
  have hA2 : 3*Cg + 3 ≤ A := le_trans (le_max_left _ _) (le_max_right _ _)
  have hA3 : 24*Cg*C₁' ≤ A := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨A, lt_of_lt_of_le (by positivity) hA1, b₁^2 + 4, by positivity, ?_⟩
  intro ε hε0 hε1 N hN f hharm hx₀ hdens r hr
  by_contra hcon
  rw [not_le] at hcon
  -- the scales
  set s : ℕ := Nat.sqrt N with hsdef
  have hssm : s * s ≤ N := by
    have h := Nat.sqrt_le' N
    rw [pow_two] at h
    rw [hsdef]; exact h
  have hb₁s : b₁ ≤ s := by
    rw [hsdef, Nat.le_sqrt]
    nlinarith [hN, Nat.zero_le b₁]
  have hs2 : 2 ≤ s := le_trans hb₁2 hb₁s
  have hs0 : 0 < s := by omega
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
      have : ((N:ℕ):ℝ) ≤ (((s+1)^2 : ℕ):ℝ) := by exact_mod_cast h1.le
      push_cast at this ⊢; nlinarith [this]
    nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ ((N:ℕ):ℝ)),
      Real.sqrt_nonneg ((N:ℕ):ℝ), hsR1]
  have hsqrt1 : (1:ℝ) ≤ Real.sqrt N := le_trans hsR1 hsle
  -- the outer square of the orbit box
  set Sn : ℕ := b₁ * s with hSndef
  have hSn4 : 4 ≤ Sn := by
    have : 2*2 ≤ b₁*s := Nat.mul_le_mul hb₁2 hs2
    omega
  have hSnR : (4:ℝ) ≤ (Sn:ℝ) := by exact_mod_cast hSn4
  have hSncast : (Sn:ℝ) = (b₁:ℝ)*(s:ℝ) := by rw [hSndef]; push_cast; ring
  have hSn1 : Real.sqrt N ≤ (Sn:ℝ) := by
    rw [hSncast]; nlinarith [hNlt, hb₁R, hsR0]
  have hSn2 : Sn ≤ 2*N := by
    have h1 : b₁ * s ≤ s * s := Nat.mul_le_mul_right s hb₁s
    rw [hSndef]; omega
  -- the derivative scale
  set R : ℝ := r/3 with hRdef
  have hrb : 3*(b₁:ℝ) * Real.sqrt N ≤ r :=
    le_trans (mul_le_mul_of_nonneg_right hA1 (Real.sqrt_nonneg _)) hr
  have hrc : (3*Cg + 3) * Real.sqrt N ≤ r :=
    le_trans (mul_le_mul_of_nonneg_right hA2 (Real.sqrt_nonneg _)) hr
  have hrd : (24*Cg*C₁') * Real.sqrt N ≤ r :=
    le_trans (mul_le_mul_of_nonneg_right hA3 (Real.sqrt_nonneg _)) hr
  have hRS : (Sn:ℝ) ≤ R := by
    rw [hRdef, hSncast, le_div_iff₀ (by norm_num : (0:ℝ) < 3)]
    have h1 : (b₁:ℝ)*(s:ℝ)*3 ≤ (b₁:ℝ)*Real.sqrt N*3 := by
      have : (0:ℝ) ≤ (b₁:ℝ)*3 := by positivity
      nlinarith [hsle]
    have h2 : (b₁:ℝ)*Real.sqrt N*3 = 3*(b₁:ℝ)*Real.sqrt N := by ring
    linarith [hrb]
  have hR1 : (1:ℝ) ≤ R := by
    rw [hRdef, le_div_iff₀ (by norm_num : (0:ℝ) < 3)]
    have h1 : (3:ℝ) ≤ (3*Cg+3) * Real.sqrt N := by nlinarith [hsqrt1, hCg0.le]
    linarith [hrc]
  have hRCg : Cg ≤ R := by
    rw [hRdef, le_div_iff₀ (by norm_num : (0:ℝ) < 3)]
    have h1 : Cg*3 ≤ (3*Cg+3) * Real.sqrt N := by nlinarith [hsqrt1, hCg0.le]
    linarith [hrc]
  have hR0 : (0:ℝ) < R := by linarith
  have hRlarge : 8*(s:ℝ)*Cg*C₁' ≤ R := by
    rw [hRdef, le_div_iff₀ (by norm_num : (0:ℝ) < 3)]
    have h1 : 8*(s:ℝ)*Cg*C₁'*3 ≤ 8*Real.sqrt N*Cg*C₁'*3 := by
      have h0 : (0:ℝ) ≤ 8*Cg*C₁'*3 := by positivity
      nlinarith [hsle]
    have h2 : 8*Real.sqrt N*Cg*C₁'*3 = (24*Cg*C₁')*Real.sqrt N := by ring
    linarith [hrd]
  have h3R : (3:ℝ)*R = r := by rw [hRdef]; ring
  -- the increment threshold
  set δ : ℝ := 1/(8*(s:ℝ)) with hδdef
  have hδ0 : (0:ℝ) ≤ δ := by rw [hδdef]; positivity
  have hδT : 2*(s:ℝ)*δ ≤ 1/4 := by
    rw [hδdef, mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  -- the bound on the maximum, assumed for contradiction
  have hmax : UCPlanar.supNorm (P.square (3*R)) f ≤ C₁' := by
    rw [h3R]
    exact le_trans hcon.le (le_max_left _ _)
  have hgrad : ∀ y : V, y ∈ P.square R → ∀ a : LatticeProb.Site 2,
      (a = vec 1 0 ∨ a = vec 0 1) → |f (P.shift a y) - f y| ≤ δ := by
    intro y hy a ha
    have hlap : ∀ x ∈ P.square (3*R),
        LatticeProb.Network.netLaplacian P.graph c f x = 0 :=
      fun x _ => hharm x (Set.mem_univ x)
    have h := hCg R hR1 hRCg f hlap y hy a ha
    have hstep : (Cg/R) * UCPlanar.supNorm (P.square (3*R)) f ≤ (Cg/R) * C₁' :=
      mul_le_mul_of_nonneg_left hmax (by positivity)
    have hfin : (Cg/R) * C₁' ≤ δ := by
      rw [hδdef, div_mul_eq_mul_div, div_le_div_iff₀ hR0 (by positivity)]
      nlinarith [hRlarge]
    linarith
  -- the orbit box lies in the square of radius `Sn`
  obtain ⟨x₀, hx₀mem, hx₀val⟩ := hx₀
  have hall : ∀ p q : ℤ, |p| ≤ (s:ℤ) → |q| ≤ (s:ℤ) →
      P.shift (vec p q) x₀ ∈ P.square (Sn:ℝ) := by
    intro p q hpq hqq
    have h := orbit_in_square P B hB0 hB x₀ ((s:ℕ):ℝ) hx₀mem s p q hpq hqq
    refine UCPlanar.Support.square_mono P ?_ h
    rw [hSncast]
    nlinarith [hBb₁, hsR0]
  have hallR : ∀ p q : ℤ, |p| ≤ (s:ℤ) → |q| ≤ (s:ℤ) →
      P.shift (vec p q) x₀ ∈ P.square R :=
    fun p q hp' hq' => UCPlanar.Support.square_mono P hRS (hall p q hp' hq')
  -- the density at the outer square and the count of the orbit box
  have hdensS : 1 - ε ≤ UCPlanar.boundedDensity (P.square (Sn:ℝ)) f 1 :=
    hdens Sn hSn1 hSn2
  have hcount : ε * (((P.square (Sn:ℝ)).card : ℕ) : ℝ) < (((2*s+1)^2 : ℕ) : ℝ) := by
    have hcard : (((P.square (Sn:ℝ)).card : ℕ) : ℝ) ≤ Cup * (Sn:ℝ)^2 :=
      hCup (Sn:ℝ) (by linarith)
    have hlt : ε * (Cup * (b₁:ℝ)^2) < 4 := by
      rw [lt_div_iff₀ (by positivity)] at hε1
      linarith [hε1]
    have heq : ε * (Cup * (Sn:ℝ)^2) = (ε * (Cup * (b₁:ℝ)^2)) * (s:ℝ)^2 := by
      rw [hSncast]; ring
    have hεb : ε * (Cup * (Sn:ℝ)^2) < 4 * (s:ℝ)^2 := by
      rw [heq]
      exact mul_lt_mul_of_pos_right hlt (by positivity)
    have h2 : (((2*s+1)^2 : ℕ) : ℝ) = (2*(s:ℝ)+1)^2 := by push_cast; ring
    rw [h2]
    nlinarith [hcard, hεb, hε0.le, hsR0]
  -- every lattice increment inside the orbit box is small
  have hrow : ∀ p q : ℤ, |p| ≤ (s:ℤ) → |p+1| ≤ (s:ℤ) → |q| ≤ (s:ℤ) →
      |f (P.shift (vec 1 0) (P.shift (vec p q) x₀)) - f (P.shift (vec p q) x₀)| ≤ δ :=
    fun p q hp' _ hq' => hgrad _ (hallR p q hp' hq') (vec 1 0) (Or.inl rfl)
  have hcol : ∀ q : ℤ, |q| ≤ (s:ℤ) → |q+1| ≤ (s:ℤ) →
      |f (P.shift (vec 0 1) (P.shift (vec 0 q) x₀)) - f (P.shift (vec 0 q) x₀)| ≤ δ :=
    fun q hq' _ => hgrad _ (hallR 0 q (by simp) hq') (vec 0 1) (Or.inr rfl)
  exact small_increments_contradict P f x₀ (Sn:ℝ) ε δ s hδ0 hx₀val hδT hall hdensS
    hcount hrow hcol

end UCPlanar.Support.Lower
