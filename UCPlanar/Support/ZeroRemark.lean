/- The remark after the zero case: the density hypothesis may be replaced by a bound on the
nonzero vertices near one sphere of admissible radius. -/
import UCPlanar.Support.ZeroAssemble
import Mathlib

open scoped BigOperators Classical

namespace UCPlanar.Support

/-- **The zero case from one sparse shell, granted the boundary cycles of Step 3.**  The
argument of Step 3 uses the density hypothesis only through the radius `m` of Step 2 and the
bound on the nonzero vertices within the buffer of the sphere of radius `m`; a bound `c₀ n` on
that count, for one admissible radius, already contradicts the linear length of the cycle that a
nonzero vertex of `B_n` forces. -/
theorem zeroCase_of_sparseShell_core {V : Type*} (Q : UCPlanar.PeriodicPlaneGraph V) (K r : ℕ)
    (hsur : Q.HasSurroundingCycles K r) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (c : V → V → ℝ), LatticeProb.Network.IsCond Q.graph c →
      ∀ (o : V) (n : ℕ), n₀ ≤ n → ∀ f : V → ℝ,
        LatticeProb.Network.HarmonicOn Q.graph c f
          (LatticeProb.Graph.closedBall Q.graph o (K*n)) →
        ∀ m : ℕ, 3 * n ≤ 2 * m → m + 2 * r ≤ 2 * n →
        ((((Q.toPeriodicGraph.ball o (2*n)).filter (fun x => f x ≠ 0 ∧
            m ≤ Q.graph.dist o x + 2 * r ∧ Q.graph.dist o x ≤ m + 2 * r)).card : ℝ) ≤ c₀ * n) →
        ∀ x ∈ Q.toPeriodicGraph.ball o n, f x = 0 := by
  classical
  obtain ⟨L, hL⟩ := Q.bounded_faces
  obtain ⟨d, hd⟩ := exists_degree_bound Q.toPeriodicGraph
  obtain ⟨κ, C₀, hκ, hC₀, hstep3⟩ := surround_step3 Q d L r hd hL
  set mult : ℝ := (((r + 1) * (d + 1) ^ r : ℕ) : ℝ) with hmultdef
  have hmult0 : 0 ≤ mult := by positivity
  have hden : (0:ℝ) < 4 * (mult + 1) := by positivity
  refine ⟨κ / (4 * (mult + 1)), by positivity, max 1 (⌈2*C₀/κ⌉₊ + 1), by omega, ?_⟩
  intro c hc o n hn f hharm m hm1 hm2 hmcount x hx
  by_contra hfx
  have hn1 : 0 < n := by omega
  have hnbig : 2 * C₀ / κ < (n : ℝ) := by
    have h1 : 2 * C₀ / κ ≤ (⌈2*C₀/κ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈2*C₀/κ⌉₊ : ℕ) + 1 ≤ n := by omega
    have h3 : ((⌈2*C₀/κ⌉₊ : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h2
    linarith
  set S : Finset V := (Q.toPeriodicGraph.ball o (2*n)).filter (fun y => f y ≠ 0 ∧
    m ≤ Q.graph.dist o y + 2 * r ∧ Q.graph.dist o y ≤ m + 2 * r) with hSdef
  have hS : ∀ y, y ∉ {x : V | |f x| ≤ 0} → m ≤ Q.graph.dist o y + r →
      Q.graph.dist o y ≤ m + r → y ∈ S := by
    intro y hfy h1 h2
    have hfy' : f y ≠ 0 := by
      simp only [Set.mem_setOf_eq, not_le] at hfy
      exact abs_pos.mp hfy
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
  have hmulle : (S.card : ℝ) * mult ≤ κ / (4 * (mult + 1)) * (n : ℝ) * mult :=
    mul_le_mul_of_nonneg_right hmcount hmult0
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hεlt : κ / (4 * (mult + 1)) < κ / (2 * (1 * mult + 1)) := by
    rw [one_mul]
    exact div_lt_div_of_pos_left hκ (by positivity) (by linarith)
  have h1 : κ * (n : ℝ) ≤ 1 * (κ / (4 * (mult + 1))) * (n : ℝ) * mult + C₀ := by
    rw [one_mul]
    linarith [hlower, hmulle]
  exact numeric_contradiction κ C₀ 1 mult (n : ℝ) (κ / (4 * (mult + 1))) hκ hC₀ hmult0
    zero_le_one hnR (by positivity) h1 hεlt hnbig

end UCPlanar.Support
