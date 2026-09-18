/-
One rung of the chain of three-ball inequalities.

The maximum of `|f|` over a square is attained at a vertex, that vertex lies in a small square
centred at a lattice point, and the three-ball inequality at that small square bounds the
maximum by the maximum over a square whose radius is larger by a fixed multiple of the small
radius.  This is the inequality `M_i ≤ C M_{i+1}^{1/2} + C exp(-cK/A) M_{i+1}` of the source.
-/
import UCPlanar.Support.LowerVolume
import UCPlanar.Support.LowerArith

open scoped BigOperators Classical
set_option autoImplicit false

namespace UCPlanar.Support.Lower

/-- The maximum of `|f|` over a nonempty finite set is attained. -/
theorem exists_max {V : Type*} (S : Finset V) (hS : S.Nonempty) (f : V → ℝ) :
    ∃ x ∈ S, UCPlanar.supNorm S f = |f x| := by
  classical
  obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_sup S hS (fun y => ‖f y‖₊)
  refine ⟨x, hx, ?_⟩
  rw [UCPlanar.supNorm, hxe]
  simp [Real.norm_eq_abs]

/-- A vertex of `Q_r` whose lattice centre is within `ρ` bounds the drawing of that centre, so
every square of radius `S` at that centre sits inside `Q_{S+r+ρ}`. -/
theorem squareAt_subset_square {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (a : LatticeProb.Site 2) (ρ r S : ℝ) (x : V) (hx : x ∈ P.square r)
    (hxa : x ∈ squareAt P a ρ) : squareAt P a S ⊆ P.square (S + r + ρ) := by
  classical
  have hw : P.shift (-a) x ∈ P.square ρ := (mem_squareAt P a ρ x).mp hxa
  have hwi : ∀ i, |P.pos (P.shift (-a) x) i| ≤ ρ :=
    (UCPlanar.Support.mem_square_iff P ρ _).mp hw
  have hxi : ∀ i, |P.pos x i| ≤ r := (UCPlanar.Support.mem_square_iff P r x).mp hx
  have hper : ∀ i, |P.period (fun j => ((a j : ℤ) : ℝ)) i| ≤ r + ρ := by
    intro i
    have hkey : P.pos x = P.pos (P.shift (-a) x) + P.period (fun j => ((a j : ℤ) : ℝ)) := by
      conv_lhs => rw [show x = P.shift a (P.shift (-a) x) from by
        rw [← P.shift_add, add_neg_cancel, P.shift_zero]]
      rw [P.pos_shift]
    have h3 : P.pos x i = P.pos (P.shift (-a) x) i + P.period (fun j => ((a j : ℤ) : ℝ)) i := by
      simpa using congrFun hkey i
    have h4 : P.period (fun j => ((a j : ℤ) : ℝ)) i
        = P.pos x i - P.pos (P.shift (-a) x) i := by linarith
    rw [h4]
    calc |P.pos x i - P.pos (P.shift (-a) x) i|
        ≤ |P.pos x i| + |P.pos (P.shift (-a) x) i| := abs_sub _ _
      _ ≤ r + ρ := add_le_add (hxi i) (hwi i)
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  rw [UCPlanar.Support.mem_square_iff]
  intro i
  rw [P.pos_shift]
  have hzi : |P.pos z i| ≤ S := (UCPlanar.Support.mem_square_iff P S z).mp hz i
  calc |P.pos z i + P.period (fun j => ((a j : ℤ) : ℝ)) i|
      ≤ |P.pos z i| + |P.period (fun j => ((a j : ℤ) : ℝ)) i| := abs_add_le _ _
    _ ≤ S + (r + ρ) := add_le_add hzi (hper i)
    _ = S + r + ρ := by ring

/-- The supremum norm is nonnegative. -/
theorem supNorm_nonneg {V : Type*} (S : Finset V) (f : V → ℝ) : 0 ≤ UCPlanar.supNorm S f := by
  unfold UCPlanar.supNorm
  exact (S.sup (fun x => ‖f x‖₊)).coe_nonneg

/-- Every value is bounded by the supremum norm. -/
theorem le_supNorm {V : Type*} (S : Finset V) (f : V → ℝ) (x : V) (hx : x ∈ S) :
    |f x| ≤ UCPlanar.supNorm S f := by
  classical
  have h1 : ‖f x‖₊ ≤ S.sup (fun y => ‖f y‖₊) := Finset.le_sup (f := fun y => ‖f y‖₊) hx
  have h2 : ((‖f x‖₊ : NNReal) : ℝ) ≤ ((S.sup (fun y => ‖f y‖₊) : NNReal) : ℝ) := by
    exact_mod_cast h1
  simpa [UCPlanar.supNorm, Real.norm_eq_abs] using h2

/-- **One rung of the chain of three-ball inequalities.**  The maximum of `|f|` over `Q_r` is
attained at a vertex, that vertex lies in the square of radius `ρ` at some lattice point, and the
three-ball inequality there bounds the maximum by the one over `Q_{Rad}`. -/
theorem chain_rung {V : Type*} (P : UCPlanar.PeriodicGraph V) (c : V → V → ℝ) (f : V → ℝ)
    (ρ : ℝ) (hcentre : ∀ x : V, ∃ a : LatticeProb.Site 2, x ∈ squareAt P a ρ)
    (k : ℕ) (hk : 1 ≤ k) (c₀ C ε : ℝ)
    (htb : ∀ (N : ℕ), 0 < N → ∀ (g : V → ℝ) (M : ℝ), 0 ≤ M → ∀ a : LatticeProb.Site 2,
        LatticeProb.Network.HarmonicOn P.graph c g (squareAt P a ((k:ℝ)*(N:ℝ)) : Set V) →
        1 - ε ≤ UCPlanar.boundedDensity (squareAt P a (N:ℝ)) g 1 →
        (∀ y ∈ squareAt P a ((k:ℝ)*(N:ℝ)), |g y| ≤ M) →
        ∀ y ∈ squareAt P a (2*(N:ℝ)), |g y| ≤ C*Real.sqrt M + C*Real.exp (-c₀*(N:ℝ))*M)
    (hharm : LatticeProb.Network.HarmonicOn P.graph c f Set.univ)
    (L : ℕ) (hL : 0 < L) (hρL : ρ ≤ (L:ℝ)) (r Rad : ℝ)
    (hRad : (k:ℝ)*(L:ℝ) + r + ρ ≤ Rad)
    (hdens : ∀ a : LatticeProb.Site 2, squareAt P a (L:ℝ) ⊆ P.square Rad →
       1 - ε ≤ UCPlanar.boundedDensity (squareAt P a (L:ℝ)) f 1)
    (hne : (P.square r).Nonempty) :
    UCPlanar.supNorm (P.square r) f
      ≤ C * Real.sqrt (UCPlanar.supNorm (P.square Rad) f)
        + C * Real.exp (-c₀*(L:ℝ)) * UCPlanar.supNorm (P.square Rad) f := by
  classical
  obtain ⟨x, hx, hmax⟩ := exists_max (P.square r) hne f
  obtain ⟨a, ha⟩ := hcentre x
  set M : ℝ := UCPlanar.supNorm (P.square Rad) f with hMdef
  have hM0 : 0 ≤ M := supNorm_nonneg _ _
  have hLk : (L:ℝ) ≤ (k:ℝ)*(L:ℝ) := by
    have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    nlinarith [Nat.cast_nonneg (α := ℝ) L]
  have hsubk : squareAt P a ((k:ℝ)*(L:ℝ)) ⊆ P.square Rad := by
    refine subset_trans (squareAt_subset_square P a ρ r ((k:ℝ)*(L:ℝ)) x hx ha) ?_
    exact UCPlanar.Support.square_mono P hRad
  have hsubL : squareAt P a (L:ℝ) ⊆ P.square Rad :=
    subset_trans (squareAt_mono P a hLk) hsubk
  have hbound : ∀ y ∈ squareAt P a ((k:ℝ)*(L:ℝ)), |f y| ≤ M :=
    fun y hy => le_supNorm _ f y (hsubk hy)
  have hharm' : LatticeProb.Network.HarmonicOn P.graph c f
      (squareAt P a ((k:ℝ)*(L:ℝ)) : Set V) := fun y _ => hharm y (Set.mem_univ y)
  have hkey := htb L hL f M hM0 a hharm' (hdens a hsubL) hbound
  have hx2 : x ∈ squareAt P a (2*(L:ℝ)) := by
    refine squareAt_mono P a ?_ ha
    linarith [hρL, Nat.cast_nonneg (α := ℝ) L]
  have := hkey x hx2
  rw [hmax]
  exact this

/-- **Proposition 2.2 of the source on a periodic graph.**  Between the scales `K` and `2K` the
chain of thirteen three-ball inequalities either contains one exponential gain, which adds
`c₀L/2` to the logarithm of the maximum, or consists of square-root losses only, which multiply
that logarithm by `32`. -/
theorem prop22 {V : Type*} (P : UCPlanar.PeriodicGraph V) (c : V → V → ℝ) (f : V → ℝ)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hcentre : ∀ x : V, ∃ a : LatticeProb.Site 2, x ∈ squareAt P a ρ)
    (k : ℕ) (hk : 1 ≤ k) (c₀ C ε C₁ : ℝ) (hC : 0 < C) (hc₀ : 0 < c₀)
    (htb : ∀ (N : ℕ), 0 < N → ∀ (g : V → ℝ) (M : ℝ), 0 ≤ M → ∀ a : LatticeProb.Site 2,
        LatticeProb.Network.HarmonicOn P.graph c g (squareAt P a ((k:ℝ)*(N:ℝ)) : Set V) →
        1 - ε ≤ UCPlanar.boundedDensity (squareAt P a (N:ℝ)) g 1 →
        (∀ y ∈ squareAt P a ((k:ℝ)*(N:ℝ)), |g y| ≤ M) →
        ∀ y ∈ squareAt P a (2*(N:ℝ)), |g y| ≤ C*Real.sqrt M + C*Real.exp (-c₀*(N:ℝ))*M)
    (hharm : LatticeProb.Network.HarmonicOn P.graph c f Set.univ)
    (hC₁ : (2*C)^4 ≤ C₁) (hC₁1 : 1 < C₁)
    (L : ℕ) (hL : 0 < L) (hρL : ρ ≤ (L:ℝ))
    (hCt : 2*C ≤ Real.exp (c₀*(L:ℝ)/2))
    (K : ℝ) (hK : 0 < K) (hfit : 13*(ρ + (k:ℝ)*(L:ℝ)) ≤ K)
    (hm0 : C₁ ≤ UCPlanar.supNorm (P.square K) f)
    (hdens : ∀ a : LatticeProb.Site 2, squareAt P a (L:ℝ) ⊆ P.square (2*K) →
       1 - ε ≤ UCPlanar.boundedDensity (squareAt P a (L:ℝ)) f 1)
    (hne : (P.square K).Nonempty) :
    min (32 * Real.log (UCPlanar.supNorm (P.square K) f))
        (Real.log (UCPlanar.supNorm (P.square K) f) + c₀*(L:ℝ)/2)
      ≤ Real.log (UCPlanar.supNorm (P.square (2*K)) f) := by
  classical
  set d : ℝ := ρ + (k:ℝ)*(L:ℝ) with hd
  have hd0 : 0 ≤ d := by
    have : (0:ℝ) ≤ (k:ℝ)*(L:ℝ) := by positivity
    simp [hd]; linarith
  set m : ℕ → ℝ := fun i => UCPlanar.supNorm (P.square (K + (i:ℝ)*d)) f with hm
  have hrle : ∀ i : ℕ, i ≤ 13 → K + (i:ℝ)*d ≤ 2*K := by
    intro i hi
    have h1 : (i:ℝ) ≤ 13 := by exact_mod_cast hi
    nlinarith [hd0, hfit, h1]
  have hmono : ∀ i j : ℕ, i ≤ j → j ≤ 13 → m i ≤ m j := by
    intro i j hij _
    have h1 : (i:ℝ) ≤ (j:ℝ) := by exact_mod_cast hij
    exact UCPlanar.Support.supNorm_mono
      (UCPlanar.Support.square_mono P (by nlinarith [hd0, h1])) f
  have hm0' : C₁ ≤ m 0 := by simpa [hm] using hm0
  have hrung : ∀ i, i < 13 → m i ≤ C * Real.sqrt (m (i+1))
      + C * Real.exp (-(c₀*(L:ℝ))) * m (i+1) := by
    intro i hi
    have hiK : K ≤ K + (i:ℝ)*d := by nlinarith [hd0, Nat.cast_nonneg (α := ℝ) i]
    have hnei : (P.square (K + (i:ℝ)*d)).Nonempty := by
      obtain ⟨z, hz⟩ := hne
      exact ⟨z, UCPlanar.Support.square_mono P hiK hz⟩
    have hRad : (k:ℝ)*(L:ℝ) + (K + (i:ℝ)*d) + ρ ≤ K + ((i+1 : ℕ):ℝ)*d := by
      have heq : K + ((i+1 : ℕ):ℝ)*d = (k:ℝ)*(L:ℝ) + (K + (i:ℝ)*d) + ρ := by
        simp only [hd]; push_cast; ring
      exact le_of_eq heq.symm
    have hsub2K : P.square (K + ((i+1 : ℕ):ℝ)*d) ⊆ P.square (2*K) :=
      UCPlanar.Support.square_mono P (hrle (i+1) (by omega))
    have := chain_rung P c f ρ hcentre k hk c₀ C ε htb hharm L hL hρL
      (K + (i:ℝ)*d) (K + ((i+1 : ℕ):ℝ)*d) hRad
      (fun a hsa => hdens a (subset_trans hsa hsub2K)) hnei
    have heq : Real.exp (-c₀*(L:ℝ)) = Real.exp (-(c₀*(L:ℝ))) := by ring_nf
    rw [heq] at this
    simpa [hm] using this
  have hkey := chain_dichotomy 13 m C C₁ (c₀*(L:ℝ)) hC (by positivity) (by
      have : c₀*(L:ℝ)/2 = (c₀*(L:ℝ))/2 := by ring
      rw [← this]; exact hCt) hC₁ hC₁1 hm0' hmono (by norm_num) hrung
  have hm13pos : 0 < m 13 := lt_of_lt_of_le (by linarith) (le_trans hm0' (hmono 0 13 (by omega) le_rfl))
  have hfinal : Real.log (m 13) ≤ Real.log (UCPlanar.supNorm (P.square (2*K)) f) :=
    Real.log_le_log hm13pos
      (UCPlanar.Support.supNorm_mono (UCPlanar.Support.square_mono P (hrle 13 le_rfl)) f)
  have hmid : c₀*(L:ℝ)/2 = (c₀*(L:ℝ))/2 := by ring
  rw [hmid]
  refine le_trans ?_ (le_trans hkey hfinal)
  simp [hm]

end UCPlanar.Support.Lower
