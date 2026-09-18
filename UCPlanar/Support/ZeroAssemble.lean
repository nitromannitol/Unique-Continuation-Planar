/- The zero case of Section 3, assembled from the sparse radius of Step 2 and the boundary
cycle of Step 3. -/
import UCPlanar.Support.ZeroCycle
import UCPlanar.Support.ZeroShell
import UCPlanar.Support.ZeroLower
import UCPlanar.Support.FiniteDomains
import Mathlib

open scoped BigOperators Classical

/-- **The boundary cycles of Step 3, as a property of the periodic plane graph.**  For every
harmonic function, every threshold `A`, every radius `m` whose buffer stays inside `B_{2n}` and
every vertex `x₀` of `B_n` where the function exceeds the larger threshold `B`, the filled
cluster of faces meeting the set where the function exceeds `A` has a boundary cycle with the
properties of `SurroundedBy`, after discarding the vertices whose face path reaches only the
intermediate band `A < |f| < B`.  The two displayed clauses are the observation that opens
Section 4: at a vertex where the function is small, a neighbour of large value forces a
neighbour of large value of the opposite sign; they are asked only when the band is nonempty,
because in the zero case `A = B = 0` the maximum principle supplies them.  The scale constant
`K` is the factor by which the region the cycle encloses can exceed the radius of the cycle
itself; harmonicity is asked on `B_{K n}` for that reason. -/
def UCPlanar.PeriodicPlaneGraph.HasSurroundingCycles {V : Type*}
    (Q : UCPlanar.PeriodicPlaneGraph V) (K r : ℕ) : Prop :=
  ∀ (c : V → V → ℝ), LatticeProb.Network.IsCond Q.graph c →
  ∀ (o : V) (m n : ℕ) (f : V → ℝ) (A B : ℝ) (x₀ : V), 0 ≤ A → A ≤ B →
    (A = 0 ∧ B = 0 ∨ A < B) →
    LatticeProb.Network.HarmonicOn Q.graph c f
      (LatticeProb.Graph.closedBall Q.graph o (K*n)) →
    (A < B → ∀ z, Q.graph.dist o z ≤ K*n → |f z| ≤ A →
      ∀ w, Q.graph.Adj z w → B ≤ f w → ∃ y, Q.graph.Adj z y ∧ f y < -A) →
    (A < B → ∀ z, Q.graph.dist o z ≤ K*n → |f z| ≤ A →
      ∀ w, Q.graph.Adj z w → f w ≤ -B → ∃ y, Q.graph.Adj z y ∧ A < f y) →
    1 ≤ n → 3 * n ≤ 2 * m → m + 2 * r ≤ 2 * n → Q.graph.dist o x₀ ≤ n → B < |f x₀| →
    ∃ D : Finset V, (∀ z ∈ D, Q.graph.dist o z ≤ m + r ∧
        ∃ y, Q.graph.dist z y ≤ r ∧ A < |f y| ∧ |f y| < B) ∧
      Q.SurroundedBy r {x | |f x| ≤ A} {x | A < f x} {x | f x < -A} D o m x₀

namespace UCPlanar.Support

/-- Membership in a metric ball, read through the graph distance. -/
theorem mem_ball_iff_dist {V : Type*} (P : UCPlanar.PeriodicGraph V) (o x : V) (n : ℕ) :
    x ∈ P.ball o n ↔ P.graph.dist o x ≤ n := by
  classical
  constructor
  · intro h
    obtain ⟨p, hp⟩ := exists_short_walk P o n h
    have := SimpleGraph.dist_le p.reverse
    rw [SimpleGraph.Walk.length_reverse] at this
    omega
  · intro h
    rw [mem_ball_iff]
    obtain ⟨p, hp⟩ := P.connected.exists_walk_length_eq_dist o x
    have hed : P.graph.edist x o ≤ ((p.reverse.length : ℕ) : ℕ∞) :=
      SimpleGraph.edist_le p.reverse
    have hlen : p.reverse.length ≤ n := by
      rw [SimpleGraph.Walk.length_reverse, hp]; exact h
    exact le_trans hed (by exact_mod_cast Nat.cast_le.mpr hlen)

/-- Membership in a closed ball, read through the graph distance. -/
theorem mem_closedBall_of_dist {V : Type*} (P : UCPlanar.PeriodicGraph V) (o x : V) (n : ℕ)
    (h : P.graph.dist o x ≤ n) : x ∈ LatticeProb.Graph.closedBall P.graph o n := by
  have := (mem_ball_iff_dist P o x n).mpr h
  exact (Set.Finite.mem_toFinset _).mp this

/-- A ball around a nearby centre sits inside a ball around the original centre. -/
theorem ball_subset_ball_of_dist {V : Type*} (P : UCPlanar.PeriodicGraph V) (o x : V)
    (s t k : ℕ) (hx : P.graph.dist o x ≤ k) (hst : s + k ≤ t) :
    P.ball x s ⊆ P.ball o t := by
  intro z hz
  rw [mem_ball_iff_dist] at hz ⊢
  have htri := P.connected.dist_triangle (u := o) (v := x) (w := z)
  omega

/-- The count of large values is monotone in the finite set. -/
theorem exceptionalCount_le_of_subset {V : Type*} {S T : Finset V} (h : S ⊆ T) (f : V → ℝ)
    (a : ℝ) : UCPlanar.exceptionalCount S f a ≤ UCPlanar.exceptionalCount T f a := by
  classical
  rw [UCPlanar.exceptionalCount, UCPlanar.exceptionalCount]
  exact Finset.card_le_card (Finset.filter_subset_filter _ h)

/-- **The density hypothesis transfers to a nearby centre at a smaller scale.**  A periodic
graph has metric balls of comparable quadratic volume at every centre, so a bound on the
proportion of large values in `B(o, 2n)` gives the same bound in `B(x, 2n')` for any smaller
ball inside it, at the cost of the constant factor `4 K² C₀ / c₀` when `n ≤ K n' + K`. -/
theorem density_recentre {V : Type*} (P : UCPlanar.PeriodicGraph V) {C₀ c₀ : ℝ}
    (hC₀ : 0 < C₀) (hc₀ : 0 < c₀)
    (hupper : ∀ (v : V) (s : ℕ), ((P.ball v s).card : ℝ) ≤ C₀ * (s + 1)^2)
    (hlower : ∀ (v : V) (s : ℕ), c₀ * ((s : ℝ) + 1)^2 ≤ ((P.ball v s).card : ℝ))
    (o x : V) (n n' K : ℕ) (hK : 1 ≤ K) (hn' : 1 ≤ n') (hnK : n ≤ K * n' + K)
    (hsub : P.ball x (2*n') ⊆ P.ball o (2*n))
    (f : V → ℝ) (a ε : ℝ) (hε : 0 ≤ ε)
    (hcount : (UCPlanar.exceptionalCount (P.ball o (2*n)) f a : ℝ)
      ≤ ε * (P.ball o (2*n)).card) :
    (UCPlanar.exceptionalCount (P.ball x (2*n')) f a : ℝ)
      ≤ (4*K^2*C₀/c₀) * ε * (P.ball x (2*n')).card := by
  have hmono : (UCPlanar.exceptionalCount (P.ball x (2*n')) f a : ℝ)
      ≤ (UCPlanar.exceptionalCount (P.ball o (2*n)) f a : ℝ) := by
    exact_mod_cast Nat.cast_le.mpr (exceptionalCount_le_of_subset hsub f a)
  have hU : ((P.ball o (2*n)).card : ℝ) ≤ C₀ * ((2*n : ℕ) + 1)^2 := hupper o (2*n)
  have hLo : c₀ * (((2*n' : ℕ) : ℝ) + 1)^2 ≤ ((P.ball x (2*n')).card : ℝ) := hlower x (2*n')
  have hcast1 : (((2*n : ℕ) : ℝ) + 1) = 2*(n:ℝ) + 1 := by push_cast; ring
  have hcast2 : (((2*n' : ℕ) : ℝ) + 1) = 2*(n':ℝ) + 1 := by push_cast; ring
  have hKR : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
  have hn'R : (1:ℝ) ≤ (n':ℝ) := by exact_mod_cast hn'
  have hnKR : (n:ℝ) ≤ (K:ℝ) * (n':ℝ) + (K:ℝ) := by exact_mod_cast hnK
  have hkey : 2*(n:ℝ) + 1 ≤ 2*(K:ℝ)*(2*(n':ℝ) + 1) := by nlinarith
  rw [hcast1] at hU
  rw [hcast2] at hLo
  have hNnn : (0:ℝ) ≤ 2*(n:ℝ) + 1 := by positivity
  have hMnn : (0:ℝ) ≤ 2*(n':ℝ) + 1 := by positivity
  have h1 : (UCPlanar.exceptionalCount (P.ball x (2*n')) f a : ℝ)
      ≤ ε * ((P.ball o (2*n)).card : ℝ) := le_trans hmono hcount
  have h2 : ε * ((P.ball o (2*n)).card : ℝ) ≤ ε * (C₀ * (2*(n:ℝ) + 1)^2) :=
    mul_le_mul_of_nonneg_left hU hε
  have h3 : (2*(n:ℝ) + 1)^2 ≤ (2*(K:ℝ)*(2*(n':ℝ) + 1))^2 := by nlinarith [hkey, hNnn]
  have h4 : ε * (C₀ * (2*(n:ℝ) + 1)^2) ≤ ε * (C₀ * (2*(K:ℝ)*(2*(n':ℝ) + 1))^2) := by
    have := mul_le_mul_of_nonneg_left h3 hC₀.le
    nlinarith [this, hε]
  have h5 : ε * (C₀ * (2*(K:ℝ)*(2*(n':ℝ) + 1))^2)
      = (4*(K:ℝ)^2*C₀/c₀) * ε * (c₀ * (2*(n':ℝ) + 1)^2) := by
    field_simp; ring
  have hfac : (0:ℝ) ≤ (4*(K:ℝ)^2*C₀/c₀) * ε := by positivity
  have h6 : (4*(K:ℝ)^2*C₀/c₀) * ε * (c₀ * (2*(n':ℝ) + 1)^2)
      ≤ (4*(K:ℝ)^2*C₀/c₀) * ε * ((P.ball x (2*n')).card : ℝ) :=
    mul_le_mul_of_nonneg_left hLo hfac
  linarith [h1, h2, h4, h5.le, h5.ge, h6]

/-- **Harmonicity supplies the opposite sign.**  A vertex where the function vanishes and which
has a positive neighbour has a negative neighbour as well. -/
theorem exists_opposite_neighbor {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    {c : V → V → ℝ} (hc : LatticeProb.Network.IsCond G c) {f : V → ℝ} {z : V}
    (hz : LatticeProb.Network.netLaplacian G c f z = 0) (hfz : f z = 0)
    {w : V} (hw : G.Adj z w) (hfw : 0 < f w) : ∃ y, G.Adj z y ∧ f y < 0 := by
  classical
  have hsum : ∑ y ∈ G.neighborFinset z, c z y * (f y - f z) = 0 := by
    rw [← LatticeProb.Network.netLaplacian]; exact hz
  obtain ⟨j, hj, hjlt⟩ := UCPlanar.Support.weighted_opposite (G.neighborFinset z)
    (fun y => c z y) (fun y => f y - f z)
    (fun i hi => hc.pos ((SimpleGraph.mem_neighborFinset G z i).mp hi)) hsum
    w ((SimpleGraph.mem_neighborFinset G z w).mpr hw) (by rw [hfz]; simpa using hfw)
  refine ⟨j, (SimpleGraph.mem_neighborFinset G z j).mp hj, ?_⟩
  rw [hfz] at hjlt
  simpa using hjlt

/-- The numerical contradiction that closes the zero case. -/
theorem numeric_contradiction (κ C₀ Cs mult n ε : ℝ) (hκ : 0 < κ) (_hC₀ : 0 ≤ C₀)
    (hmult : 0 ≤ mult) (hCs : 0 ≤ Cs) (hn : 0 < n) (hε : 0 ≤ ε)
    (h1 : κ * n ≤ Cs * ε * n * mult + C₀)
    (h2 : ε < κ / (2 * (Cs * mult + 1)))
    (h3 : 2 * C₀ / κ < n) : False := by
  have hd : (0:ℝ) < 2 * (Cs * mult + 1) := by nlinarith
  have hεb : ε * (2 * (Cs * mult + 1)) < κ := by
    have := (lt_div_iff₀ hd).mp h2
    linarith
  have hC : 2 * C₀ < κ * n := by
    have := (div_lt_iff₀ hκ).mp h3
    linarith
  have hprod : Cs * ε * n * mult ≤ ε * (Cs * mult + 1) * n := by nlinarith
  have hhalf : ε * (Cs * mult + 1) * n < κ * n / 2 := by nlinarith
  linarith

/-- **The zero case of Section 3, granted the boundary cycles of Step 3.**  Step 2 supplies a
radius whose buffer carries at most `C ε n` nonzero vertices; Step 3 turns a single nonzero
vertex of `B_n` into a cycle a fixed fraction of whose vertices sit in that buffer, and whose
length is linear in `n`; the two bounds are incompatible once `ε` is small and `n` large. -/
theorem zeroCase_core {V : Type*} (Q : UCPlanar.PeriodicPlaneGraph V) (K r : ℕ)
    (hsur : Q.HasSurroundingCycles K r) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (c : V → V → ℝ), LatticeProb.Network.IsCond Q.graph c →
      ∀ (o : V) (n : ℕ), n₀ ≤ n → ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ →
      ∀ f : V → ℝ,
        LatticeProb.Network.HarmonicOn Q.graph c f
          (LatticeProb.Graph.closedBall Q.graph o (K*n)) →
        (UCPlanar.exceptionalCount (Q.toPeriodicGraph.ball o (2*n)) f 0 : ℝ) ≤
          ε * (Q.toPeriodicGraph.ball o (2*n)).card →
        ∀ x ∈ Q.toPeriodicGraph.ball o n, f x = 0 := by
  classical
  obtain ⟨L, hL⟩ := Q.bounded_faces
  obtain ⟨d, hd⟩ := exists_degree_bound Q.toPeriodicGraph
  obtain ⟨κ, C₀, hκ, hC₀, hstep3⟩ := surround_step3 Q d L r hd hL
  obtain ⟨Cs, hCs, hshell⟩ := exists_sparse_shell Q.toPeriodicGraph (2*r)
  set mult : ℝ := (((r + 1) * (d + 1) ^ r : ℕ) : ℝ) with hmultdef
  have hmult0 : 0 ≤ mult := by positivity
  have hden : (0:ℝ) < 2 * (Cs * mult + 1) := by nlinarith
  refine ⟨κ / (2 * (Cs * mult + 1)), by positivity, max (max 1 (8*r)) (⌈2*C₀/κ⌉₊ + 1),
    by omega, ?_⟩
  intro c hc o n hn ε hε hεlt f hharm hcount x hx
  by_contra hfx
  have hn1 : 0 < n := by omega
  have hn8r : 4 * (2*r) ≤ n := by omega
  have hnbig : 2 * C₀ / κ < (n : ℝ) := by
    have h1 : 2 * C₀ / κ ≤ (⌈2*C₀/κ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈2*C₀/κ⌉₊ : ℕ) + 1 ≤ n := by omega
    have h3 : ((⌈2*C₀/κ⌉₊ : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h2
    linarith
  obtain ⟨m, hm1, hm2, hmcount⟩ := hshell o n hn1 hn8r 0 ε hε f hcount
  set S : Finset V := (Q.toPeriodicGraph.ball o (2*n)).filter (fun y => 0 < |f y| ∧
    m ≤ Q.graph.dist o y + 2*r ∧ Q.graph.dist o y ≤ m + 2*r) with hSdef
  have hS : ∀ y, y ∉ {x : V | |f x| ≤ 0} → m ≤ Q.graph.dist o y + r →
      Q.graph.dist o y ≤ m + r → y ∈ S := by
    intro y hfy h1 h2
    have hfy' : 0 < |f y| := by
      simp only [Set.mem_setOf_eq, not_le] at hfy
      exact hfy
    rw [hSdef, Finset.mem_filter]
    refine ⟨?_, hfy', by omega, by omega⟩
    rw [mem_ball_iff_dist]
    omega
  have hx₀ : Q.graph.dist o x ≤ n := (mem_ball_iff_dist Q.toPeriodicGraph o x n).mp hx
  have hfx' : (0:ℝ) < |f x| := abs_pos.mpr hfx
  obtain ⟨Dis, hDis, hsurr⟩ := hsur c hc o m n f 0 0 x le_rfl le_rfl (Or.inl ⟨rfl, rfl⟩) hharm
    (fun h => absurd h (lt_irrefl 0)) (fun h => absurd h (lt_irrefl 0)) hn1 hm1 hm2 hx₀ hfx'
  have hDempty : Dis = ∅ := by
    refine Finset.eq_empty_of_forall_notMem ?_
    intro z hz
    obtain ⟨-, y, -, h1, h2⟩ := hDis z hz
    linarith
  have hdWP : Disjoint {x : V | |f x| ≤ 0} {x : V | (0:ℝ) < f x} := by
    refine Set.disjoint_left.mpr ?_
    intro z hz hz2
    simp only [Set.mem_setOf_eq] at hz hz2
    have := abs_nonneg (f z)
    have : |f z| = 0 := le_antisymm hz (abs_nonneg _)
    rw [abs_eq_zero] at this
    rw [this] at hz2
    exact lt_irrefl 0 hz2
  have hdWN : Disjoint {x : V | |f x| ≤ 0} {x : V | f x < -0} := by
    refine Set.disjoint_left.mpr ?_
    intro z hz hz2
    simp only [Set.mem_setOf_eq, neg_zero] at hz hz2
    have : |f z| = 0 := le_antisymm hz (abs_nonneg _)
    rw [abs_eq_zero] at this
    rw [this] at hz2
    exact lt_irrefl 0 hz2
  have hdPN : Disjoint {x : V | (0:ℝ) < f x} {x : V | f x < -0} := by
    refine Set.disjoint_left.mpr ?_
    intro z hz hz2
    simp only [Set.mem_setOf_eq, neg_zero] at hz hz2
    linarith
  have hlower := hstep3 o m n {x : V | |f x| ≤ 0} {x : V | (0:ℝ) < f x} {x : V | f x < -0}
    Dis x S hdWP hdWN hdPN hx₀ hm1 hS hsurr
  rw [hDempty] at hlower
  simp only [Finset.card_empty, Nat.cast_zero, add_zero] at hlower
  have hupper : (S.card : ℝ) ≤ Cs * ε * n := hmcount
  have hmulle : (S.card : ℝ) * mult ≤ Cs * ε * (n : ℝ) * mult :=
    mul_le_mul_of_nonneg_right hupper hmult0
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn1
  exact numeric_contradiction κ C₀ Cs mult (n : ℝ) ε hκ hC₀ hmult0 hCs.le hnR hε
    (by linarith [hlower, hmulle]) hεlt hnbig


/-- **The zero case of Section 3 on the ball the paper states it for.**  The cycle of Step 3
encloses a region that can exceed its own radius by the scale constant `K`, so the argument runs
at the reduced scale `n / K`; the conclusion on `B_n` is recovered by re-centring at every vertex
of `B_n`, which is legitimate because the density hypothesis at the original centre implies it at
every nearby centre, at the cost of the constant factor of the volume comparison. -/
theorem zeroCase_of_surrounding {V : Type*} (Q : UCPlanar.PeriodicPlaneGraph V) (K r : ℕ)
    (hK : 2 ≤ K) (hsur : Q.HasSurroundingCycles K r) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (c : V → V → ℝ), LatticeProb.Network.IsCond Q.graph c →
      ∀ (o : V) (n : ℕ), n₀ ≤ n → ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ →
      ∀ f : V → ℝ,
        LatticeProb.Network.HarmonicOn Q.graph c f
          (LatticeProb.Graph.closedBall Q.graph o (2*n)) →
        (UCPlanar.exceptionalCount (Q.toPeriodicGraph.ball o (2*n)) f 0 : ℝ) ≤
          ε * (Q.toPeriodicGraph.ball o (2*n)).card →
        ∀ x ∈ Q.toPeriodicGraph.ball o n, f x = 0 := by
  classical
  obtain ⟨ε₁, hε₁, n₁, hn₁, hcore⟩ := zeroCase_core Q K r hsur
  obtain ⟨C₀, hC₀, hupper⟩ := exists_ball_card_bound Q.toPeriodicGraph
  obtain ⟨c₀, hc₀, hlower⟩ := exists_ball_card_lower Q.toPeriodicGraph
  have hK0 : 0 < K := by omega
  have hKR : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK0
  have hfac : (0:ℝ) < 4*(K:ℝ)^2*C₀/c₀ := by positivity
  refine ⟨ε₁ * c₀ / (4*(K:ℝ)^2*C₀), by positivity, K * (n₁ + 1), Nat.mul_pos hK0 (by omega), ?_⟩
  intro c hc o n hn ε hε hεlt f hharm hcount x hx
  set n' : ℕ := n / K with hn'def
  have hKn₁ : K * n₁ + K ≤ n := by
    have h := hn
    rw [Nat.mul_add, Nat.mul_one] at h
    exact h
  have hn'1 : n₁ ≤ n' := by
    rw [hn'def]
    refine (Nat.le_div_iff_mul_le hK0).mpr ?_
    calc n₁ * K = K * n₁ := Nat.mul_comm _ _
      _ ≤ K * n₁ + K := Nat.le_add_right _ _
      _ ≤ n := hKn₁
  have hn'pos : 1 ≤ n' := by omega
  have hKn' : K * n' ≤ n := by
    rw [hn'def, Nat.mul_comm]
    exact Nat.div_mul_le_self n K
  have hnK : n ≤ K * n' + K := by
    have hdiv : K * n' + n % K = n := by rw [hn'def]; exact Nat.div_add_mod n K
    have hmod : n % K < K := Nat.mod_lt _ hK0
    calc n = K * n' + n % K := hdiv.symm
      _ ≤ K * n' + K := Nat.add_le_add_left (le_of_lt hmod) _
  have h2n' : 2 * n' ≤ n := le_trans (Nat.mul_le_mul hK (le_refl n')) hKn'
  have hxd : Q.graph.dist o x ≤ n := (mem_ball_iff_dist Q.toPeriodicGraph o x n).mp hx
  have hsub : Q.toPeriodicGraph.ball x (2*n') ⊆ Q.toPeriodicGraph.ball o (2*n) :=
    ball_subset_ball_of_dist Q.toPeriodicGraph o x (2*n') (2*n) n hxd (by omega)
  have hharmx : LatticeProb.Network.HarmonicOn Q.graph c f
      (LatticeProb.Graph.closedBall Q.graph x (K*n')) := by
    intro z hz
    have hzb : z ∈ Q.toPeriodicGraph.ball x (K*n') := by
      have hzs : z ∈ (Q.toPeriodicGraph.ball x (K*n') : Set V) := by rw [coe_ball]; exact hz
      exact_mod_cast hzs
    have hz1 : Q.graph.dist x z ≤ K*n' :=
      (mem_ball_iff_dist Q.toPeriodicGraph x z (K*n')).mp hzb
    have hz2 : Q.graph.dist x z ≤ n := le_trans hz1 hKn'
    have htri := Q.connected.dist_triangle (u := o) (v := x) (w := z)
    exact hharm z (mem_closedBall_of_dist Q.toPeriodicGraph o z (2*n) (by omega))
  have hcountx := density_recentre Q.toPeriodicGraph hC₀ hc₀ hupper hlower o x n n' K
    (by omega) hn'pos hnK hsub f 0 ε hε hcount
  have hεx : (4*(K:ℝ)^2*C₀/c₀) * ε < ε₁ := by
    have h1 := mul_lt_mul_of_pos_left hεlt hfac
    have heq : (4*(K:ℝ)^2*C₀/c₀) * (ε₁ * c₀ / (4*(K:ℝ)^2*C₀)) = ε₁ := by
      field_simp
    linarith [h1, heq.le, heq.ge]
  refine hcore c hc x n' hn'1 ((4*(K:ℝ)^2*C₀/c₀) * ε) (by positivity) hεx f hharmx hcountx x ?_
  exact (mem_ball_iff_dist Q.toPeriodicGraph x x n').mpr (by simp)

end UCPlanar.Support
