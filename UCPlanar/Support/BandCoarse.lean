/- Step 1 of Section 4: the coarse exponential bound, from the same boundary cycles. -/
import UCPlanar.Support.BandSign
import UCPlanar.Support.Bands
import UCPlanar.Support.ZeroCycle
import UCPlanar.Support.BandsCover
import Mathlib

open scoped BigOperators Classical

namespace UCPlanar.Support

/-- Raising the threshold does not increase the exceptional count. -/
theorem exceptionalCount_mono {V : Type*} (S : Finset V) (f : V → ℝ) (a b : ℝ) (hab : a ≤ b) :
    UCPlanar.exceptionalCount S f b ≤ UCPlanar.exceptionalCount S f a := by
  classical
  unfold UCPlanar.exceptionalCount
  refine Finset.card_le_card ?_
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, lt_of_le_of_lt hab hx.2⟩

set_option maxHeartbeats 1000000 in

/-- **Step 1 of Section 4: the coarse exponential bound.**  Among the geometric bands of values
below `K ^ (2 r)` one holds at most a constant times `ε₁ r` vertices; treating the vertices
below that band as zeros and discarding the band, the boundary cycle of Step 3 forces linearly
many vertices above the band near the chosen sphere, which the sparse radius forbids. -/
theorem coarse_core {V : Type*} (Q : UCPlanar.PeriodicPlaneGraph V) (Kc r : ℕ)
    (hsur : Q.HasSurroundingCycles Kc r) :
    ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ Θ : ℝ, 1 < Θ → ∃ ε₁ a : ℝ, 0 < ε₁ ∧ 0 < a ∧
      ∀ lam : ℝ, 0 < lam → ∀ c : V → V → ℝ,
        LatticeProb.Network.IsCond Q.graph c →
        UCPlanar.UniformlyElliptic Q.graph c lam (Θ*lam) →
        ∀ (o : V) (rr : ℕ), r₀ ≤ rr → ∀ f : V → ℝ,
          LatticeProb.Network.HarmonicOn Q.graph c f
            (LatticeProb.Graph.closedBall Q.graph o (Kc*rr)) →
          ((UCPlanar.exceptionalCount (Q.toPeriodicGraph.ball o (2*rr)) f 1 : ℝ)
            ≤ ε₁ * (Q.toPeriodicGraph.ball o (2*rr)).card) →
          ∀ y ∈ Q.toPeriodicGraph.ball o rr, |f y| ≤ Real.exp (a * rr) := by
  classical
  obtain ⟨L, hL⟩ := Q.bounded_faces
  obtain ⟨d, hd⟩ := exists_degree_bound Q.toPeriodicGraph
  obtain ⟨κ, C₀, hκ, hC₀, hstep3⟩ := surround_step3 Q d L r hd hL
  obtain ⟨Cs, hCs, hshell⟩ := exists_sparse_shell Q.toPeriodicGraph (2*r)
  obtain ⟨C₂, hC₂, hballup⟩ := exists_ball_card_bound Q.toPeriodicGraph
  set mult : ℝ := (((r + 1) * (d + 1) ^ r : ℕ) : ℝ) with hmultdef
  have hmult0 : 0 < mult := by
    rw [hmultdef]
    have : 0 < (r + 1) * (d + 1) ^ r := by positivity
    exact_mod_cast this
  clear_value mult
  refine ⟨max (max 1 (8*r)) (⌈(2*(mult + C₀))/κ⌉₊ + 1), by omega, ?_⟩
  intro Θ hΘ
  set K : ℝ := 2*Θ*(d:ℝ) + 2 with hKdef
  have hd0 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg _
  have hK1 : 1 < K := by rw [hKdef]; nlinarith
  have hK0 : 0 < K := by linarith
  clear_value K
  set ε₁ : ℝ := κ / (2 * ((Cs + 9*C₂) * mult + 1)) with hε₁def
  have hT0 : 0 < (Cs + 9*C₂) * mult := mul_pos (by linarith) hmult0
  have hden : 0 < 2 * ((Cs + 9*C₂) * mult + 1) := by linarith
  have hε₁0 : 0 < ε₁ := by rw [hε₁def]; exact div_pos hκ hden
  clear_value ε₁
  set a : ℝ := 2 * Real.log K with hadef
  have ha0 : 0 < a := by
    rw [hadef]
    have : 0 < Real.log K := Real.log_pos hK1
    linarith
  clear_value a
  refine ⟨ε₁, a, hε₁0, ha0, ?_⟩
  intro lam hlam c hc hell o rr hrr f hharm hcount y hy
  by_contra hbig
  push Not at hbig
  have hrrmax : max (max 1 (8*r)) (⌈(2*(mult + C₀))/κ⌉₊ + 1) ≤ rr := hrr
  have hrr1 : 0 < rr := by omega
  have hrr8 : 4 * (2*r) ≤ rr := by omega
  have hrrbig : (2*(mult + C₀))/κ < (rr : ℝ) := by
    have h1 : (2*(mult + C₀))/κ ≤ (⌈(2*(mult + C₀))/κ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈(2*(mult + C₀))/κ⌉₊ : ℕ) + 1 ≤ rr := by omega
    have h3 : ((⌈(2*(mult + C₀))/κ⌉₊ : ℕ) : ℝ) + 1 ≤ (rr : ℝ) := by exact_mod_cast h2
    linarith
  have hKexp : (K : ℝ) ^ (2*rr) = Real.exp (a * rr) := by
    rw [hadef]
    have : a * (rr:ℝ) = ((2*rr : ℕ) : ℝ) * Real.log K := by push_cast [hadef]; ring
    rw [hadef] at this
    rw [this, mul_comm, Real.exp_nat_mul, Real.exp_log hK0]
  -- the exceptional set and the sparse band
  set Sexc : Finset V := (Q.toPeriodicGraph.ball o (2*rr)).filter (fun x => 1 < |f x|) with hSexc
  have hSexccard : (Sexc.card : ℝ) ≤ ε₁ * (Q.toPeriodicGraph.ball o (2*rr)).card := by
    have : (Sexc.card : ℝ)
        = ((UCPlanar.exceptionalCount (Q.toPeriodicGraph.ball o (2*rr)) f 1 : ℕ) : ℝ) := by
      rw [hSexc, UCPlanar.exceptionalCount]
    rw [this]; exact hcount
  have hrrR : (1:ℝ) ≤ (rr:ℝ) := by exact_mod_cast hrr1
  have hballR : ((Q.toPeriodicGraph.ball o (2*rr)).card : ℝ) ≤ 9 * C₂ * (rr:ℝ)^2 := by
    have h := hballup o (2*rr)
    have hcast : ((2*rr : ℕ) : ℝ) = 2 * (rr:ℝ) := by push_cast; ring
    rw [hcast] at h
    have hsq : (2*(rr:ℝ)+1)^2 ≤ 9*(rr:ℝ)^2 := by nlinarith [hrrR]
    have := mul_le_mul_of_nonneg_left hsq hC₂.le
    linarith [h, this]
  set δ : ℝ := 9*C₂*ε₁*(rr:ℝ) + 1 with hδdef
  have hsmall : (Sexc.card : ℝ) < δ * rr := by
    have h1 : (Sexc.card : ℝ) ≤ ε₁ * (9 * C₂ * (rr:ℝ)^2) :=
      le_trans hSexccard (mul_le_mul_of_nonneg_left hballR hε₁0.le)
    rw [hδdef]
    nlinarith [h1, hrrR]
  obtain ⟨A, hA1, hAle, hband⟩ := exists_sparse_threshold Sexc f K hK1 δ rr hrr1 hsmall
  have hA0 : 0 < A := lt_of_lt_of_le one_pos hA1
  set B : ℝ := K * A with hBdef
  have hAB : A ≤ B := by rw [hBdef]; nlinarith
  have hABlt : A < B := by rw [hBdef]; nlinarith
  clear_value B
  -- the two opposite-sign clauses
  have hopp : ∀ w : V, Q.graph.dist o w ≤ Kc*rr → |f w| ≤ A →
      ∀ v, Q.graph.Adj w v → B ≤ f v → ∃ u, Q.graph.Adj w u ∧ f u < -A := by
    intro w hw hfw v hv hfv
    exact band_exists_opposite_neighbor d hd lam Θ hlam hΘ hell A hA0
      (hharm w (mem_closedBall_of_dist Q.toPeriodicGraph o w (Kc*rr) hw)) hfw hv
      (by rw [hBdef, hKdef] at hfv; exact hfv)
  have hopp' : ∀ w : V, Q.graph.dist o w ≤ Kc*rr → |f w| ≤ A →
      ∀ v, Q.graph.Adj w v → f v ≤ -B → ∃ u, Q.graph.Adj w u ∧ A < f u := by
    intro w hw hfw v hv hfv
    exact band_exists_opposite_neighbor' d hd lam Θ hlam hΘ hell A hA0
      (hharm w (mem_closedBall_of_dist Q.toPeriodicGraph o w (Kc*rr) hw)) hfw hv
      (by rw [hBdef, hKdef] at hfv; exact hfv)
  -- the sparse radius for the threshold `A`
  have hcountA : ((UCPlanar.exceptionalCount (Q.toPeriodicGraph.ball o (2*rr)) f A : ℕ) : ℝ)
      ≤ ε₁ * (Q.toPeriodicGraph.ball o (2*rr)).card := by
    have := exceptionalCount_mono (Q.toPeriodicGraph.ball o (2*rr)) f 1 A hA1
    have hcast : ((UCPlanar.exceptionalCount (Q.toPeriodicGraph.ball o (2*rr)) f A : ℕ) : ℝ)
        ≤ ((UCPlanar.exceptionalCount (Q.toPeriodicGraph.ball o (2*rr)) f 1 : ℕ) : ℝ) := by
      exact_mod_cast this
    linarith [hcount]
  obtain ⟨m, hm1, hm2, hmcount⟩ := hshell o rr hrr1 hrr8 A ε₁ hε₁0.le f hcountA
  set S : Finset V := (Q.toPeriodicGraph.ball o (2*rr)).filter (fun x => A < |f x| ∧
    m ≤ Q.graph.dist o x + 2*r ∧ Q.graph.dist o x ≤ m + 2*r) with hSdef
  have hSmem : ∀ v, v ∉ {x : V | |f x| ≤ A} → m ≤ Q.graph.dist o v + r →
      Q.graph.dist o v ≤ m + r → v ∈ S := by
    intro v hv h1 h2
    have hvA : A < |f v| := by simpa [Set.mem_setOf_eq] using hv
    rw [hSdef, Finset.mem_filter]
    refine ⟨?_, hvA, by omega, by omega⟩
    rw [mem_ball_iff_dist]
    omega
  -- the surrounding cycle
  have hyd : Q.graph.dist o y ≤ rr := (mem_ball_iff_dist Q.toPeriodicGraph o y rr).mp hy
  have hAsmall : B < |f y| := by
    have h1 : B ≤ K ^ (2*rr) := by
      have hKpow : K * K ^ rr ≤ K ^ (2*rr) := by
        have : K ^ (rr + 1) ≤ K ^ (2*rr) := pow_le_pow_right₀ hK1.le (by omega)
        calc K * K ^ rr = K ^ (rr + 1) := by rw [pow_succ]; ring
          _ ≤ K ^ (2*rr) := this
      calc B = K * A := hBdef
        _ ≤ K * K ^ rr := by nlinarith [hAle, hK0]
        _ ≤ K ^ (2*rr) := hKpow
    rw [hKexp] at h1
    linarith [hbig]
  obtain ⟨D, hD, hsurr⟩ := hsur c hc o m rr f A B y hA0.le hAB (Or.inr hABlt) hharm
    (fun _ w hw hfw v hv hfv => hopp w hw hfw v hv hfv)
    (fun _ w hw hfw v hv hfv => hopp' w hw hfw v hv hfv)
    hrr1 hm1 hm2 hyd hAsmall
  -- the discarded vertices are charged to the sparse band
  set Band : Finset V := Sexc.filter (fun x => A ≤ |f x| ∧ |f x| < B) with hBanddef
  have hDcard : (D.card : ℝ) ≤ (Band.card : ℝ) * mult := by
    have hfil : D.filter (fun w => ∃ b ∈ Band, Q.graph.dist w b ≤ r) = D := by
      refine Finset.filter_true_of_mem ?_
      intro w hw
      obtain ⟨hwd, v, hwv, h1, h2⟩ := hD w hw
      refine ⟨v, ?_, hwv⟩
      rw [hBanddef, Finset.mem_filter, hSexc, Finset.mem_filter]
      refine ⟨⟨?_, lt_of_le_of_lt hA1 h1⟩, h1.le, ?_⟩
      · rw [mem_ball_iff_dist]
        have := Q.connected.dist_triangle (u := o) (v := w) (w := v)
        omega
      · exact h2
    have hmain := UCPlanar.Support.card_near_boundary_le Q.connected D Band d r hd
    rw [hfil] at hmain
    have : (D.card : ℝ) ≤ (Band.card : ℝ) * (((r + 1) * (d + 1) ^ r : ℕ) : ℝ) := by
      exact_mod_cast hmain
    rw [hmultdef]; exact this
  have hBandcard : (Band.card : ℝ) < δ := hband
  -- the two bounds are incompatible
  have hdWP : Disjoint {x : V | |f x| ≤ A} {x : V | A < f x} := by
    refine Set.disjoint_left.mpr ?_
    intro v h1 h2
    simp only [Set.mem_setOf_eq] at h1 h2
    have := le_trans (le_abs_self (f v)) h1
    linarith
  have hdWN : Disjoint {x : V | |f x| ≤ A} {x : V | f x < -A} := by
    refine Set.disjoint_left.mpr ?_
    intro v h1 h2
    simp only [Set.mem_setOf_eq] at h1 h2
    have := le_trans (neg_le_abs (f v)) h1
    linarith
  have hdPN : Disjoint {x : V | A < f x} {x : V | f x < -A} := by
    refine Set.disjoint_left.mpr ?_
    intro v h1 h2
    simp only [Set.mem_setOf_eq] at h1 h2
    linarith
  have hlower := hstep3 o m rr {x : V | |f x| ≤ A} {x : V | A < f x} {x : V | f x < -A}
    D y S hdWP hdWN hdPN hyd hm1 hSmem hsurr
  have hScard : (S.card : ℝ) ≤ Cs * ε₁ * rr := hmcount
  have hmulS : (S.card : ℝ) * mult ≤ Cs * ε₁ * (rr:ℝ) * mult :=
    mul_le_mul_of_nonneg_right hScard hmult0.le
  have hDb : (D.card : ℝ) ≤ δ * mult :=
    le_trans hDcard (mul_le_mul_of_nonneg_right hBandcard.le hmult0.le)
  have hne : (Cs + 9*C₂) * mult + 1 ≠ 0 := by linarith
  have hprod : ε₁ * ((Cs + 9*C₂) * mult + 1) = κ / 2 := by
    rw [hε₁def, ← div_div, div_mul_cancel₀ _ hne]
  have hε₁small : ε₁ * ((Cs + 9*C₂) * mult) < κ / 2 := by
    have hring : ε₁ * ((Cs + 9*C₂) * mult + 1)
        = ε₁ * ((Cs + 9*C₂) * mult) + ε₁ := by ring
    linarith [hprod, hring, hε₁0]
  have hlast : mult + C₀ < κ * rr / 2 := by
    have := (div_lt_iff₀ hκ).mp hrrbig
    linarith
  have hrrpos : (0:ℝ) < (rr:ℝ) := by linarith [hrrR]
  have hmix : ε₁ * ((Cs + 9*C₂) * mult) * (rr:ℝ) < (κ/2) * (rr:ℝ) :=
    mul_lt_mul_of_pos_right hε₁small hrrpos
  have hexpand : Cs * ε₁ * (rr:ℝ) * mult + δ * mult
      = ε₁ * ((Cs + 9*C₂) * mult) * (rr:ℝ) + mult := by rw [hδdef]; ring
  linarith [hlower, hmulS, hDb, hmix, hlast, hexpand.le, hexpand.ge]

/-- **The coarse exponential bound on the ball the rescaling is applied to.**  The same
re-centring as in the zero case: the cycle of Step 3 encloses a region that can exceed its own
radius by the scale constant, so the bound runs at the reduced radius `rr / Kc` and is read off
at each vertex of `B_rr` with that vertex as the centre. -/
theorem coarse_of_surrounding {V : Type*} (Q : UCPlanar.PeriodicPlaneGraph V) (Kc r : ℕ)
    (hK : 2 ≤ Kc) (hsur : Q.HasSurroundingCycles Kc r) :
    ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ Θ : ℝ, 1 < Θ → ∃ ε₁ a : ℝ, 0 < ε₁ ∧ 0 < a ∧
      ∀ lam : ℝ, 0 < lam → ∀ c : V → V → ℝ,
        LatticeProb.Network.IsCond Q.graph c →
        UCPlanar.UniformlyElliptic Q.graph c lam (Θ*lam) →
        ∀ (o : V) (rr : ℕ), r₀ ≤ rr → ∀ f : V → ℝ,
          LatticeProb.Network.HarmonicOn Q.graph c f
            (LatticeProb.Graph.closedBall Q.graph o (2*rr)) →
          ((UCPlanar.exceptionalCount (Q.toPeriodicGraph.ball o (2*rr)) f 1 : ℝ)
            ≤ ε₁ * (Q.toPeriodicGraph.ball o (2*rr)).card) →
          ∀ y ∈ Q.toPeriodicGraph.ball o rr, |f y| ≤ Real.exp (a * rr) := by
  classical
  obtain ⟨r₁, hr₁, hcore⟩ := coarse_core Q Kc r hsur
  obtain ⟨C₀, hC₀, hupper⟩ := exists_ball_card_bound Q.toPeriodicGraph
  obtain ⟨c₀, hc₀, hlower⟩ := exists_ball_card_lower Q.toPeriodicGraph
  have hK0 : 0 < Kc := by omega
  have hKR : (0:ℝ) < (Kc:ℝ) := by exact_mod_cast hK0
  have hfac : (0:ℝ) < 4*(Kc:ℝ)^2*C₀/c₀ := by positivity
  refine ⟨Kc * (r₁ + 1), Nat.mul_pos hK0 (by omega), ?_⟩
  intro Θ hΘ
  obtain ⟨ε₁, a, hε₁, ha, hcb⟩ := hcore Θ hΘ
  have heq : (4*(Kc:ℝ)^2*C₀/c₀) * (ε₁ * c₀ / (4*(Kc:ℝ)^2*C₀)) = ε₁ := by field_simp
  refine ⟨ε₁ * c₀ / (4*(Kc:ℝ)^2*C₀), a, by positivity, ha, ?_⟩
  intro lam hlam c hcond hell o rr hrr f hharm hcount y hy
  set rr' : ℕ := rr / Kc with hrr'def
  have hKr₁ : Kc * r₁ + Kc ≤ rr := by
    have h := hrr
    rw [Nat.mul_add, Nat.mul_one] at h
    exact h
  have hrr'1 : r₁ ≤ rr' := by
    rw [hrr'def]
    refine (Nat.le_div_iff_mul_le hK0).mpr ?_
    calc r₁ * Kc = Kc * r₁ := Nat.mul_comm _ _
      _ ≤ Kc * r₁ + Kc := Nat.le_add_right _ _
      _ ≤ rr := hKr₁
  have hrr'pos : 1 ≤ rr' := by omega
  have hKrr' : Kc * rr' ≤ rr := by
    rw [hrr'def, Nat.mul_comm]
    exact Nat.div_mul_le_self rr Kc
  have hrrK : rr ≤ Kc * rr' + Kc := by
    have hdiv : Kc * rr' + rr % Kc = rr := by rw [hrr'def]; exact Nat.div_add_mod rr Kc
    have hmod : rr % Kc < Kc := Nat.mod_lt _ hK0
    calc rr = Kc * rr' + rr % Kc := hdiv.symm
      _ ≤ Kc * rr' + Kc := Nat.add_le_add_left (le_of_lt hmod) _
  have h2rr' : 2 * rr' ≤ rr := le_trans (Nat.mul_le_mul hK (le_refl rr')) hKrr'
  have hyd : Q.graph.dist o y ≤ rr := (mem_ball_iff_dist Q.toPeriodicGraph o y rr).mp hy
  have hsub : Q.toPeriodicGraph.ball y (2*rr') ⊆ Q.toPeriodicGraph.ball o (2*rr) :=
    ball_subset_ball_of_dist Q.toPeriodicGraph o y (2*rr') (2*rr) rr hyd (by omega)
  have hharmy : LatticeProb.Network.HarmonicOn Q.graph c f
      (LatticeProb.Graph.closedBall Q.graph y (Kc*rr')) := by
    intro z hz
    have hzb : z ∈ Q.toPeriodicGraph.ball y (Kc*rr') := by
      have hzs : z ∈ (Q.toPeriodicGraph.ball y (Kc*rr') : Set V) := by rw [coe_ball]; exact hz
      exact_mod_cast hzs
    have hz1 : Q.graph.dist y z ≤ Kc*rr' :=
      (mem_ball_iff_dist Q.toPeriodicGraph y z (Kc*rr')).mp hzb
    have hz2 : Q.graph.dist y z ≤ rr := le_trans hz1 hKrr'
    have htri := Q.connected.dist_triangle (u := o) (v := y) (w := z)
    exact hharm z (mem_closedBall_of_dist Q.toPeriodicGraph o z (2*rr) (by omega))
  have hcounty : ((UCPlanar.exceptionalCount (Q.toPeriodicGraph.ball y (2*rr')) f 1 : ℕ) : ℝ)
      ≤ ε₁ * (Q.toPeriodicGraph.ball y (2*rr')).card := by
    have h := density_recentre Q.toPeriodicGraph hC₀ hc₀ hupper hlower o y rr rr' Kc
      (by omega) hrr'pos hrrK hsub f 1 (ε₁ * c₀ / (4*(Kc:ℝ)^2*C₀)) (by positivity) hcount
    rw [heq] at h
    exact h
  have hyy : y ∈ Q.toPeriodicGraph.ball y rr' :=
    (mem_ball_iff_dist Q.toPeriodicGraph y y rr').mpr (by simp)
  have hbd := hcb lam hlam c hcond hell y rr' hrr'1 f hharmy hcounty y hyy
  refine le_trans hbd (Real.exp_le_exp.mpr ?_)
  have hle : (rr' : ℝ) ≤ (rr : ℝ) := by exact_mod_cast (by omega : rr' ≤ rr)
  nlinarith [ha, hle]

/-- **The uniform upper bound of Section 4, granted the boundary cycles of Step 3.**  The coarse
exponential bound of Step 1 is rescaled by Step 2.  The minimum radius comes from the geometry
alone, so it is fixed before the ellipticity ratio. -/
theorem uniformlyBounded_of_surrounding {V : Type*} (Q : UCPlanar.PeriodicPlaneGraph V)
    (Kc r : ℕ) (hK : 2 ≤ Kc) (hsur : Q.HasSurroundingCycles Kc r) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ Θ : ℝ, 1 < Θ →
      ∃ ε₀ A : ℝ, 0 < ε₀ ∧ 0 < A ∧
      ∀ (lam : ℝ), 0 < lam → ∀ (c : V → V → ℝ),
      LatticeProb.Network.IsCond Q.graph c →
      UCPlanar.UniformlyElliptic Q.graph c lam (Θ*lam) →
      ∀ (o : V) (n : ℕ), n₀ ≤ n → ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ →
      ∀ f : V → ℝ,
        LatticeProb.Network.HarmonicOn Q.graph c f
          (LatticeProb.Graph.closedBall Q.graph o (2*n)) →
        (UCPlanar.exceptionalCount (Q.toPeriodicGraph.ball o (2*n)) f 1 : ℝ) ≤
          ε * (Q.toPeriodicGraph.ball o (2*n)).card →
        ∀ x ∈ Q.toPeriodicGraph.ball o n, |f x| ≤ Real.exp (A * Real.sqrt ε * n) := by
  obtain ⟨r₀, hr₀, hcoarse⟩ := coarse_of_surrounding Q Kc r hK hsur
  refine ⟨max (2*r₀) 4, by omega, ?_⟩
  intro Θ hΘ
  obtain ⟨ε₁, a, hε₁, ha, hc⟩ := hcoarse Θ hΘ
  exact uniformlyBounded_of_coarse Q.toPeriodicGraph r₀ hr₀ Θ ε₁ a hε₁ ha hc

end UCPlanar.Support
