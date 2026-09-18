/- The maximum principle in a finite domain: few exceptional vertices force a bound. -/
import UCPlanar.Support.ZeroVolume
import UCPlanar.Support.ZeroCount
import UCPlanar.Support.ZeroSign
import UCPlanar.Basic
import Mathlib

open scoped BigOperators Classical

namespace UCPlanar.Support

/-- **Subtracting a constant does not change the Laplacian.** -/
theorem netLaplacian_sub_const {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    (c : V → V → ℝ) (f : V → ℝ) (A : ℝ) (x : V) :
    LatticeProb.Network.netLaplacian G c (fun z => f z - A) x
      = LatticeProb.Network.netLaplacian G c f x := by
  classical
  simp only [LatticeProb.Network.netLaplacian]
  refine Finset.sum_congr rfl ?_
  intro y _
  ring

/-- **The Laplacian of the negative.** -/
theorem netLaplacian_neg {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    (c : V → V → ℝ) (f : V → ℝ) (x : V) :
    LatticeProb.Network.netLaplacian G c (fun z => -f z) x
      = - LatticeProb.Network.netLaplacian G c f x := by
  classical
  simp only [LatticeProb.Network.netLaplacian, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro y _
  ring

/-- Membership in a metric ball, unfolded. -/
theorem mem_ball_iff {V : Type*} (P : UCPlanar.PeriodicGraph V) (o x : V) (n : ℕ) :
    x ∈ P.ball o n ↔ P.graph.edist x o ≤ (n : ℕ∞) := by
  classical
  constructor
  · intro h
    have := (Set.Finite.mem_toFinset _).mp h
    simpa [LatticeProb.Graph.closedBall] using this
  · intro h
    refine (Set.Finite.mem_toFinset _).mpr ?_
    simpa [LatticeProb.Graph.closedBall] using h

/-- **A large value forces many exceptional vertices.**  If `f` exceeds `A` somewhere in `B_n`
and is harmonic on `B_{2n}`, the component of the superlevel set through that vertex runs to the
boundary of `B_{2n}` by the maximum principle, so more than `n` vertices of `B_{2n}` carry
`|f| > A`. -/
theorem exceptional_gt_of_large {V : Type*} (P : UCPlanar.PeriodicGraph V)
    {c : V → V → ℝ} (hc : LatticeProb.Network.IsCond P.graph c)
    (o : V) (n : ℕ) (A : ℝ) (f : V → ℝ)
    (hharm : ∀ z ∈ P.ball o (2*n), LatticeProb.Network.netLaplacian P.graph c f z = 0)
    (x : V) (hx : x ∈ P.ball o n) (hgt : A < f x) :
    (n : ℝ) < ((((P.ball o (2*n)).filter (fun z => A < |f z|)).card : ℕ) : ℝ) := by
  classical
  haveI := infinite_of_periodic P
  have hgharm : ∀ z ∈ P.ball o (2*n),
      LatticeProb.Network.netLaplacian P.graph c (fun z => f z - A) z = 0 := by
    intro z hz
    rw [netLaplacian_sub_const]
    exact hharm z hz
  have hx2 : x ∈ P.ball o (2*n) := by
    rw [mem_ball_iff] at hx ⊢
    refine le_trans hx ?_
    exact_mod_cast Nat.cast_le.mpr (by omega : n ≤ 2*n)
  obtain ⟨w, p, hsupp, y, hwy, hyS⟩ :=
    exists_positive_path_to_boundary P.connected hc (P.ball o (2*n)) (fun z => f z - A)
      hgharm x hx2 (by simpa using sub_pos.mpr hgt)
  obtain ⟨p₀, hp₀⟩ := exists_short_walk P o n hx
  have hsubE : ∀ z ∈ p.support, z ∈ (P.ball o (2*n)).filter (fun z => A < |f z|) := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hsupp z hz
    refine Finset.mem_filter.mpr ⟨hz1, ?_⟩
    have hz2' : 0 < f z - A := hz2
    have hfz : A < f z := by linarith
    exact lt_of_lt_of_le hfz (le_abs_self _)
  have hcard := card_ge_of_walk ((P.ball o (2*n)).filter (fun z => A < |f z|)) p hsubE
  have hlen : ∀ q : P.graph.Walk x w, n ≤ q.length := by
    intro q
    by_contra hq
    push Not at hq
    have hed : P.graph.edist y o ≤ ((q.length + p₀.length + 1 : ℕ) : ℕ∞) := by
      have hw := SimpleGraph.edist_le (SimpleGraph.Walk.cons hwy.symm (q.reverse.append p₀))
      simpa [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse] using hw
    have hle2 : q.length + p₀.length + 1 ≤ 2*n := by omega
    refine hyS ?_
    rw [mem_ball_iff]
    refine le_trans hed ?_
    exact_mod_cast Nat.cast_le.mpr hle2
  obtain ⟨q, hq⟩ := P.connected.exists_walk_length_eq_dist x w
  have hdist : n ≤ P.graph.dist x w := by rw [← hq]; exact hlen q
  have hfin : n + 1 ≤ ((P.ball o (2*n)).filter (fun z => A < |f z|)).card := by omega
  exact_mod_cast Nat.lt_of_succ_le hfin

/-- **Few exceptional vertices force a bound.**  The contrapositive of the previous estimate:
at most `n` vertices of `B_{2n}` with `|f| > A` give `|f| ≤ A` throughout `B_n`.  This is the
argument that handles the scales below the minimum radius in Section 4. -/
theorem le_of_few_exceptional {V : Type*} (P : UCPlanar.PeriodicGraph V)
    {c : V → V → ℝ} (hc : LatticeProb.Network.IsCond P.graph c)
    (o : V) (n : ℕ) (A : ℝ) (f : V → ℝ)
    (hharm : ∀ z ∈ P.ball o (2*n), LatticeProb.Network.netLaplacian P.graph c f z = 0)
    (hfew : ((UCPlanar.exceptionalCount (P.ball o (2*n)) f A : ℕ) : ℝ) ≤ n) :
    ∀ x ∈ P.ball o n, |f x| ≤ A := by
  classical
  intro x hx
  by_contra hcon
  push Not at hcon
  have hcount : (((P.ball o (2*n)).filter (fun z => A < |f z|)).card : ℝ) ≤ (n : ℝ) := by
    rw [UCPlanar.exceptionalCount] at hfew
    exact hfew
  rcases lt_abs.mp hcon with h | h
  · have := exceptional_gt_of_large P hc o n A f hharm x hx h
    linarith
  · have hharm' : ∀ z ∈ P.ball o (2*n),
        LatticeProb.Network.netLaplacian P.graph c (fun z => -f z) z = 0 := by
      intro z hz
      rw [netLaplacian_neg, hharm z hz, neg_zero]
    have hb := exceptional_gt_of_large P hc o n A (fun z => -f z) hharm' x hx (by simpa using h)
    have heq : (P.ball o (2*n)).filter (fun z => A < |(-f z)|)
        = (P.ball o (2*n)).filter (fun z => A < |f z|) := by
      refine Finset.filter_congr ?_
      intro z _
      rw [abs_neg]
    rw [heq] at hb
    linarith

end UCPlanar.Support
