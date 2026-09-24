/-
The contradiction that closes the Liouville theorem.

A nonconstant harmonic function with a bounded-value density close to one is unbounded, by the
classical bounded-Liouville fact, so after a change of sign it is at least `2` at one vertex, and
that vertex lies in the small square `Q_{⌊√N⌋}` for every large `N`.  The exponential lower bound
then forces `exp(bN)` on `Q_N`, while the uniform upper bound on a graph ball containing `Q_N`
forces `exp(A√ε n)` with `n` linear in `N`.  The two are incompatible once `ε` is small compared
with `b / (A C)`, where `C` is the LINEAR constant of the comparison of squares with balls.
-/
import UCPlanar.Support.LowerAssembly
import UCPlanar.Support.ZeroAssemble
import UCPlanar.Support.ZeroMax
import UCPlanar.Support.ThreeAssembly
import UCPlanar.Support.Growth
import UCPlanar.Support.LiouFinalGeom

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace UCPlanar.Support.LiouFinal

/-- Graph balls grow with the radius. -/
theorem ball_mono {V : Type*} (P : UCPlanar.PeriodicGraph V) (o : V) {n m : ℕ} (h : n ≤ m) :
    P.ball o n ⊆ P.ball o m := by
  intro x hx
  rw [UCPlanar.Support.mem_ball_iff_dist] at hx ⊢
  exact le_trans hx (by exact_mod_cast h)

/-- A bounded-value density at least `1 - ε` gives, at every large radius, an exceptional count
below any fixed fraction above `ε`. -/
theorem eventually_exceptional {V : Type*} (P : UCPlanar.PeriodicGraph V) (o : V) (g : V → ℝ)
    (ε t : ℝ) (hεt : ε < t) (hdens : P.HasBoundedDensity o g ε) :
    ∀ᶠ m : ℕ in Filter.atTop,
      (UCPlanar.exceptionalCount (P.ball o m) g 1 : ℝ) ≤ t * ((P.ball o m).card : ℝ) := by
  classical
  obtain ⟨d, hd, htend⟩ := hdens
  have hlt : (1:ℝ) - t < d := by linarith
  have h1 : ∀ᶠ m : ℕ in Filter.atTop,
      1 - t < UCPlanar.boundedDensity (P.ball o m) g 1 :=
    htend.eventually (eventually_gt_nhds hlt)
  refine h1.mono ?_
  intro m hm
  set S : Finset V := P.ball o m with hS
  have hSne : S.Nonempty := by
    refine ⟨o, ?_⟩
    rw [hS, UCPlanar.Support.mem_ball_iff_dist]
    simp
  have hSpos : (0:ℝ) < (S.card : ℝ) := by
    have : 0 < S.card := Finset.card_pos.mpr hSne
    exact_mod_cast this
  have hsplit : ((S.filter (fun x => |g x| ≤ 1)).card : ℝ)
      + ((S.filter (fun x => ¬ (|g x| ≤ 1))).card : ℝ) = (S.card : ℝ) := by
    have := Finset.card_filter_add_card_filter_not (s := S) (p := fun x => |g x| ≤ 1)
    exact_mod_cast this
  have hexc : UCPlanar.exceptionalCount S g 1 = (S.filter (fun x => ¬ (|g x| ≤ 1))).card := by
    rw [UCPlanar.exceptionalCount]
    congr 1
    apply Finset.filter_congr
    intro x _
    simp [not_le]
  have hgood : (1 - t) * (S.card : ℝ) < ((S.filter (fun x => |g x| ≤ 1)).card : ℝ) := by
    have h2 := hm
    rw [UCPlanar.boundedDensity, lt_div_iff₀ hSpos] at h2
    linarith
  rw [hexc]
  linarith

/-- **The Liouville theorem from the two bounds.**  The hypotheses `hUB` and `hLB` are the
conclusions of the uniform upper bound and of the exponential lower bound, `hBL` is the classical
bounded-Liouville input, `hgeo` compares squares with balls with a multiplicative constant that
does not depend on the base point, and `hsq` transfers the density from balls to squares. -/
theorem liouville_final {V : Type*} (P : UCPlanar.PeriodicPlaneGraph V)
    (c : V → V → ℝ) (hc : LatticeProb.Network.IsCond P.graph c)
    (lam Θ : ℝ) (hlam : 0 < lam) (hΘ : 1 < Θ)
    (hell : UCPlanar.UniformlyElliptic P.graph c lam (Θ*lam))
    (hUB : ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ Θ : ℝ, 1 < Θ →
      ∃ ε₀ A : ℝ, 0 < ε₀ ∧ 0 < A ∧
      ∀ (lam : ℝ), 0 < lam → ∀ (c : V → V → ℝ),
      LatticeProb.Network.IsCond P.graph c → UCPlanar.UniformlyElliptic P.graph c lam (Θ*lam) →
      ∀ (o : V) (n : ℕ), n₀ ≤ n → ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ →
      ∀ f : V → ℝ,
        LatticeProb.Network.HarmonicOn P.graph c f
          (LatticeProb.Graph.closedBall P.graph o (2*n)) →
        (UCPlanar.exceptionalCount (P.toPeriodicGraph.ball o (2*n)) f 1 : ℝ) ≤
          ε * (P.toPeriodicGraph.ball o (2*n)).card →
        ∀ x ∈ P.toPeriodicGraph.ball o n, |f x| ≤ Real.exp (A * Real.sqrt ε * n))
    (hLB : ∃ b : ℝ, 0 < b ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ N : ℕ, N₀ ≤ N → ∀ f : V → ℝ,
        LatticeProb.Network.HarmonicOn P.graph c f Set.univ →
        (∃ x ∈ P.toPeriodicGraph.square (Nat.sqrt N), 2 ≤ f x) →
        (∀ K : ℕ, Real.sqrt N ≤ K → K ≤ 2*N →
          1 - ε ≤ UCPlanar.boundedDensity (P.toPeriodicGraph.square K) f 1) →
        Real.exp (b*N) ≤ UCPlanar.supNorm (P.toPeriodicGraph.square N) f)
    (hBL : ∀ f : V → ℝ, LatticeProb.Network.HarmonicOn P.graph c f Set.univ →
      (∃ M : ℝ, ∀ x, |f x| ≤ M) → ∃ a : ℝ, ∀ x, f x = a)
    (hgeo : ∃ Cg : ℝ, 0 < Cg ∧ ∀ o : V, ∃ c₂ : ℝ, 0 ≤ c₂ ∧ ∀ R : ℝ, 0 ≤ R →
      ∃ n : ℕ, (n:ℝ) ≤ Cg*R + c₂ ∧
        (P.toPeriodicGraph.square R : Set V) ⊆ (P.toPeriodicGraph.ball o n : Set V))
    (hsq : ∃ Ctr : ℝ, 0 < Ctr ∧ ∀ (o : V) (f : V → ℝ) (ε : ℝ), 0 < ε →
      P.toPeriodicGraph.HasBoundedDensity o f ε →
      ∀ᶠ N : ℕ in Filter.atTop, ∀ K : ℕ, Real.sqrt N ≤ K → K ≤ 2*N →
        1 - Ctr*ε ≤ UCPlanar.boundedDensity (P.toPeriodicGraph.square K) f 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (o : V) (f : V → ℝ),
      LatticeProb.Network.HarmonicOn P.graph c f Set.univ →
      P.toPeriodicGraph.HasBoundedDensity o f ε → ∃ a : ℝ, ∀ x, f x = a := by
  classical
  obtain ⟨n₀, hn₀, hUBΘ⟩ := hUB
  obtain ⟨ε₀U, A, hε₀U, hA, hUB2⟩ := hUBΘ Θ hΘ
  obtain ⟨b, hb, ε₀L, hε₀L, N₀, hN₀, hLB2⟩ := hLB
  obtain ⟨Cg, hCg, hgeo2⟩ := hgeo
  obtain ⟨Ctr, hCtr0, hsq2⟩ := hsq
  set εs : ℝ := min (min (ε₀L/(2*Ctr)) (ε₀U/4)) ((b/(2*A*Cg))^2/2) with hεsdef
  have hεs0 : 0 < εs := by rw [hεsdef]; positivity
  have hεsL : Ctr*εs < ε₀L := by
    have h1 : εs ≤ ε₀L/(2*Ctr) := le_trans (min_le_left _ _) (min_le_left _ _)
    have h2 : Ctr*εs ≤ Ctr*(ε₀L/(2*Ctr)) := mul_le_mul_of_nonneg_left h1 hCtr0.le
    have h3 : Ctr*(ε₀L/(2*Ctr)) = ε₀L/2 := by field_simp
    linarith
  have hεsU : 2*εs < ε₀U := by
    have h1 : εs ≤ ε₀U/4 := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have hεsB : 2*εs ≤ (b/(2*A*Cg))^2 := by
    have h1 : εs ≤ (b/(2*A*Cg))^2/2 := min_le_right _ _
    linarith
  have hroot : A * Real.sqrt (2*εs) ≤ b/(2*Cg) := by
    have h1 : Real.sqrt (2*εs) ≤ b/(2*A*Cg) := by
      have h2 : Real.sqrt (2*εs) ≤ Real.sqrt ((b/(2*A*Cg))^2) := Real.sqrt_le_sqrt hεsB
      rwa [Real.sqrt_sq (by positivity)] at h2
    have h3 : A * Real.sqrt (2*εs) ≤ A * (b/(2*A*Cg)) := mul_le_mul_of_nonneg_left h1 hA.le
    have h4 : A * (b/(2*A*Cg)) = b/(2*Cg) := by field_simp
    linarith
  refine ⟨εs, hεs0, ?_⟩
  intro o f hharm hdens
  by_contra hnc
  -- a nonconstant harmonic function is unbounded
  have hunb : ¬ (∃ M : ℝ, ∀ x, |f x| ≤ M) := fun hM => hnc (hBL f hharm hM)
  have hzex : ∃ z : V, 2 < |f z| := by
    by_contra h
    refine hunb ⟨2, fun x => ?_⟩
    by_contra hx
    exact h ⟨x, not_le.mp hx⟩
  obtain ⟨z, hz2⟩ := hzex
  -- it is enough to contradict a function that is at least 2 somewhere
  suffices H : ∀ g : V → ℝ, LatticeProb.Network.HarmonicOn P.graph c g Set.univ →
      P.toPeriodicGraph.HasBoundedDensity o g εs → (∃ w : V, 2 ≤ g w) → False by
    by_cases hpos : 0 ≤ f z
    · refine H f hharm hdens ⟨z, ?_⟩
      rw [abs_of_nonneg hpos] at hz2
      exact le_of_lt hz2
    · have hneg : f z < 0 := not_le.mp hpos
      refine H (fun x => -f x) ?_ ?_ ⟨z, ?_⟩
      · intro x _
        rw [UCPlanar.Support.netLaplacian_neg, hharm x (Set.mem_univ x), neg_zero]
      · obtain ⟨d, hd, htend⟩ := hdens
        refine ⟨d, hd, ?_⟩
        have heq : ∀ m : ℕ, UCPlanar.boundedDensity (P.toPeriodicGraph.ball o m)
            (fun x => -f x) 1 = UCPlanar.boundedDensity (P.toPeriodicGraph.ball o m) f 1 := by
          intro m; simp [UCPlanar.boundedDensity, abs_neg]
        simpa [heq] using htend
      · rw [abs_of_neg hneg] at hz2; linarith
  intro g hg hgd hgw
  obtain ⟨w, hgw2⟩ := hgw
  obtain ⟨c₂, hc₂0, hgeoN⟩ := hgeo2 o
  -- the two eventual facts
  obtain ⟨m₁, hm₁⟩ := Filter.eventually_atTop.mp
    (eventually_exceptional P.toPeriodicGraph o g εs (2*εs) (by linarith) hgd)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hsq2 o g εs hεs0 hgd)
  set M : ℕ := max n₀ m₁ with hMdef
  set ζ : ℕ := ⌈‖P.toPeriodicGraph.pos w‖⌉₊ with hζdef
  set Nm : ℕ := ⌈(M:ℝ)/Cg⌉₊ with hNmdef
  set Nc : ℕ := ⌈c₂/Cg⌉₊ + 1 with hNcdef
  set N : ℕ := max (max N₀ N₁) (max (max (ζ*ζ) Nc) Nm) with hNdef
  have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
  have hNN₁ : N₁ ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
  have hNζ : ζ*ζ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
  have hNNc : Nc ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
  have hNNm : Nm ≤ N := le_trans (le_max_right _ _) (le_max_right _ _)
  have hNpos : 0 < N := lt_of_lt_of_le hN₀ hNN₀
  have hNR0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNpos
  -- the vertex of size two lies in the small square
  have hwsq : w ∈ P.toPeriodicGraph.square (Nat.sqrt N) := by
    rw [UCPlanar.Support.mem_square_iff]
    intro i
    have h1 : ζ ≤ Nat.sqrt N := Nat.le_sqrt.mpr hNζ
    have h2 : ‖P.toPeriodicGraph.pos w‖ ≤ (ζ:ℝ) := Nat.le_ceil _
    have h3 : ((ζ:ℕ):ℝ) ≤ ((Nat.sqrt N : ℕ):ℝ) := by exact_mod_cast h1
    have h4 : |P.toPeriodicGraph.pos w i| ≤ ‖P.toPeriodicGraph.pos w‖ := by
      have := norm_le_pi_norm (P.toPeriodicGraph.pos w) i
      rwa [Real.norm_eq_abs] at this
    linarith
  -- the lower bound at the scale N
  have hlow : Real.exp (b*N) ≤ UCPlanar.supNorm (P.toPeriodicGraph.square N) g :=
    hLB2 (Ctr*εs) (by positivity) hεsL N hNN₀ g hg ⟨w, hwsq, hgw2⟩ (hN₁ N hNN₁)
  -- the ball that contains the square
  obtain ⟨n, hnle, hsub⟩ := hgeoN (N:ℝ) (le_of_lt hNR0)
  set nn : ℕ := max n M with hnndef
  have hMle : (M:ℝ) ≤ Cg*(N:ℝ) + c₂ := by
    have h1 : (M:ℝ)/Cg ≤ (Nm:ℝ) := Nat.le_ceil _
    have h2 : ((Nm:ℕ):ℝ) ≤ (N:ℝ) := by exact_mod_cast hNNm
    have h3 : (M:ℝ)/Cg ≤ (N:ℝ) := le_trans h1 h2
    rw [div_le_iff₀ hCg] at h3
    linarith
  have hnnle : (nn:ℝ) ≤ Cg*(N:ℝ) + c₂ := by
    rw [hnndef, Nat.cast_max]
    exact max_le hnle hMle
  have hnn₀ : n₀ ≤ nn := le_trans (le_max_left _ _) (le_max_right n M)
  have hnnm₁ : m₁ ≤ 2*nn := by
    have : m₁ ≤ M := le_max_right _ _
    have : m₁ ≤ nn := le_trans this (le_max_right n M)
    omega
  have hsubF : P.toPeriodicGraph.square (N:ℝ) ⊆ P.toPeriodicGraph.ball o nn := by
    intro x hx
    exact ball_mono P.toPeriodicGraph o (le_max_left n M) (by exact_mod_cast hsub hx)
  -- the upper bound on that ball
  have hup := hUB2 lam hlam c hc hell o nn hnn₀ (2*εs) (by positivity) hεsU g
    (fun x _ => hg x (Set.mem_univ x)) (hm₁ (2*nn) hnnm₁)
  have hupsq : UCPlanar.supNorm (P.toPeriodicGraph.square N) g
      ≤ Real.exp (A * Real.sqrt (2*εs) * nn) :=
    UCPlanar.Support.Three.supNorm_le _ g _ (Real.exp_nonneg _)
      (fun x hx => hup x (hsubF hx))
  -- the two bounds are incompatible
  have hexpineq : b*(N:ℝ) ≤ A * Real.sqrt (2*εs) * (nn:ℝ) :=
    Real.exp_le_exp.mp (le_trans hlow hupsq)
  have hnn0 : (0:ℝ) ≤ (nn:ℝ) := Nat.cast_nonneg _
  have hchain : A * Real.sqrt (2*εs) * (nn:ℝ) ≤ (b/(2*Cg)) * (Cg*(N:ℝ) + c₂) := by
    have h1 : A * Real.sqrt (2*εs) * (nn:ℝ) ≤ (b/(2*Cg)) * (nn:ℝ) :=
      mul_le_mul_of_nonneg_right hroot hnn0
    have h2 : (b/(2*Cg)) * (nn:ℝ) ≤ (b/(2*Cg)) * (Cg*(N:ℝ) + c₂) :=
      mul_le_mul_of_nonneg_left hnnle (by positivity)
    linarith
  have hNcgt : c₂/Cg < (N:ℝ) := by
    have h1 : c₂/Cg ≤ ((⌈c₂/Cg⌉₊ : ℕ):ℝ) := Nat.le_ceil _
    have h2 : ((Nc:ℕ):ℝ) ≤ (N:ℝ) := by exact_mod_cast hNNc
    have h3 : ((⌈c₂/Cg⌉₊ : ℕ):ℝ) + 1 = ((Nc:ℕ):ℝ) := by rw [hNcdef]; push_cast; ring
    linarith
  have h4 : c₂ < (N:ℝ)*Cg := by rwa [div_lt_iff₀ hCg] at hNcgt
  have key : b*(N:ℝ) ≤ (b/(2*Cg))*(Cg*(N:ℝ) + c₂) := le_trans hexpineq hchain
  have hexpand : (b/(2*Cg))*(Cg*(N:ℝ) + c₂) = b*(N:ℝ)/2 + b*c₂/(2*Cg) := by
    field_simp
  rw [hexpand] at key
  have h5 : b*c₂/(2*Cg) < b*(N:ℝ)/2 := by
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2*Cg)]
    linarith [mul_lt_mul_of_pos_left h4 hb]
  linarith

/-- **The Liouville theorem with the geometric comparison discharged.**  Only the uniform upper
bound, the exponential lower bound, the bounded-Liouville input and the transfer of the density
from balls to squares remain as hypotheses. -/
theorem liouville_final_of_density {V : Type*} (P : UCPlanar.PeriodicPlaneGraph V)
    (c : V → V → ℝ) (hc : LatticeProb.Network.IsCond P.graph c)
    (lam Θ : ℝ) (hlam : 0 < lam) (hΘ : 1 < Θ)
    (hell : UCPlanar.UniformlyElliptic P.graph c lam (Θ*lam))
    (hUB : ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ Θ : ℝ, 1 < Θ →
      ∃ ε₀ A : ℝ, 0 < ε₀ ∧ 0 < A ∧
      ∀ (lam : ℝ), 0 < lam → ∀ (c : V → V → ℝ),
      LatticeProb.Network.IsCond P.graph c → UCPlanar.UniformlyElliptic P.graph c lam (Θ*lam) →
      ∀ (o : V) (n : ℕ), n₀ ≤ n → ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ →
      ∀ f : V → ℝ,
        LatticeProb.Network.HarmonicOn P.graph c f
          (LatticeProb.Graph.closedBall P.graph o (2*n)) →
        (UCPlanar.exceptionalCount (P.toPeriodicGraph.ball o (2*n)) f 1 : ℝ) ≤
          ε * (P.toPeriodicGraph.ball o (2*n)).card →
        ∀ x ∈ P.toPeriodicGraph.ball o n, |f x| ≤ Real.exp (A * Real.sqrt ε * n))
    (hLB : ∃ b : ℝ, 0 < b ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ N : ℕ, N₀ ≤ N → ∀ f : V → ℝ,
        LatticeProb.Network.HarmonicOn P.graph c f Set.univ →
        (∃ x ∈ P.toPeriodicGraph.square (Nat.sqrt N), 2 ≤ f x) →
        (∀ K : ℕ, Real.sqrt N ≤ K → K ≤ 2*N →
          1 - ε ≤ UCPlanar.boundedDensity (P.toPeriodicGraph.square K) f 1) →
        Real.exp (b*N) ≤ UCPlanar.supNorm (P.toPeriodicGraph.square N) f)
    (hBL : ∀ f : V → ℝ, LatticeProb.Network.HarmonicOn P.graph c f Set.univ →
      (∃ M : ℝ, ∀ x, |f x| ≤ M) → ∃ a : ℝ, ∀ x, f x = a)
    (hsq : ∃ Ctr : ℝ, 0 < Ctr ∧ ∀ (o : V) (f : V → ℝ) (ε : ℝ), 0 < ε →
      P.toPeriodicGraph.HasBoundedDensity o f ε →
      ∀ᶠ N : ℕ in Filter.atTop, ∀ K : ℕ, Real.sqrt N ≤ K → K ≤ 2*N →
        1 - Ctr*ε ≤ UCPlanar.boundedDensity (P.toPeriodicGraph.square K) f 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (o : V) (f : V → ℝ),
      LatticeProb.Network.HarmonicOn P.graph c f Set.univ →
      P.toPeriodicGraph.HasBoundedDensity o f ε → ∃ a : ℝ, ∀ x, f x = a :=
  liouville_final P c hc lam Θ hlam hΘ hell hUB hLB hBL
    (exists_square_ball_uniform P.toPeriodicGraph) hsq

end UCPlanar.Support.LiouFinal
