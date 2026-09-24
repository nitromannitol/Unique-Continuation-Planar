/- The boundary cycles of Step 3 as a property of the graph: the two closed forms of Step 3
supply them, and the harmonicity they ask for inside the cycle is available because a cycle
confined to the buffer of the sphere of radius `m` encloses only vertices within a graph
constant times `m`. -/
import UCPlanar.Support.TopoStep3Closed
import Mathlib

open scoped Classical

namespace UCPlanar.Support

variable {V : Type*}

/-- **Step 3 holds on every periodic plane graph, at the buffer radius `L + 1` and at a scale
constant fixed by the face bound and the enclosure bound.**  The zero case and the banded case
are the two clauses of the definition; in both the cycle produced by the filled cluster lies
within `m + L` of the centre, so the region it encloses lies within `C (m + L) + C`, which the
scale constant is chosen to absorb. -/
theorem exists_hasSurroundingCycles (Q : UCPlanar.PeriodicPlaneGraph V)
    (hES : UCPlanar.External.EdgeSplitting Q.embedding)
    (hU : UCPlanar.External.Unicoherence Q.embedding) :
    ∃ Kc r : ℕ, 2 ≤ Kc ∧ Q.HasSurroundingCycles Kc r := by
  classical
  obtain ⟨L, hL⟩ := Q.bounded_faces
  obtain ⟨Cc, hCc0, hCc⟩ := exists_dist_le_of_cycleRegion_dist Q
  refine ⟨max 2 ⌈2*Cc + Cc*(L:ℝ) + Cc⌉₊, L + 1, le_max_left _ _, ?_⟩
  set Kc : ℕ := max 2 ⌈2*Cc + Cc*(L:ℝ) + Cc⌉₊ with hKcdef
  have hKc2 : 2 ≤ Kc := le_max_left _ _
  have hKcR : 2*Cc + Cc*(L:ℝ) + Cc ≤ (Kc:ℝ) := by
    have hceil : 2*Cc + Cc*(L:ℝ) + Cc ≤ ((⌈2*Cc + Cc*(L:ℝ) + Cc⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hmax : (⌈2*Cc + Cc*(L:ℝ) + Cc⌉₊ : ℕ) ≤ Kc := le_max_right _ _
    have hcast : ((⌈2*Cc + Cc*(L:ℝ) + Cc⌉₊ : ℕ) : ℝ) ≤ (Kc:ℝ) := by exact_mod_cast hmax
    linarith
  intro c hc o m n f A B x₀ hA0 hAB hcase hharm hupc hdnc hn1 hm1 hm2 hx₀ hfx₀
  have hmn : m ≤ 2*n := by omega
  have hnm : n ≤ m := by omega
  have h2Kc : 2*n ≤ Kc*n := Nat.mul_le_mul hKc2 (le_refl n)
  have hmKc : m ≤ Kc*n := le_trans hmn h2Kc
  -- harmonicity on the cluster ball
  have hharmm : ∀ z ∈ Q.toPeriodicGraph.ball o m,
      LatticeProb.Network.netLaplacian Q.graph c f z = 0 := by
    intro z hz
    have hd : Q.graph.dist o z ≤ m := (mem_ball_iff_dist Q.toPeriodicGraph o z m).mp hz
    exact hharm z (mem_closedBall_of_dist Q.toPeriodicGraph o z (Kc*n) (le_trans hd hmKc))
  -- every vertex a confined cycle encloses stays inside the harmonicity ball
  have hgeo : ∀ (b : V) (γ : Q.graph.Walk b b),
      (∀ w ∈ γ.support, Q.graph.dist o w ≤ m + L) →
      ∀ z ∈ Q.embedding.cycleRegion γ, Q.graph.dist o z ≤ Kc * n := by
    intro b γ hsupp z hz
    have h1 := hCc o b γ (m + L) hsupp z hz
    have hmR : ((m:ℝ)) ≤ 2*(n:ℝ) := by exact_mod_cast hmn
    have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
    have hLR : (0:ℝ) ≤ (L:ℝ) := Nat.cast_nonneg _
    have hcastk : ((m + L : ℕ) : ℝ) = (m:ℝ) + (L:ℝ) := by push_cast; ring
    rw [hcastk] at h1
    have hnn : (0:ℝ) ≤ Cc*(L:ℝ) + Cc := by nlinarith
    have s1 : Cc * ((m:ℝ) + (L:ℝ)) + Cc ≤ Cc * (2*(n:ℝ) + (L:ℝ)) + Cc := by
      nlinarith [mul_nonneg hCc0.le (by linarith : (0:ℝ) ≤ 2*(n:ℝ) - (m:ℝ))]
    have s3 : Cc*(L:ℝ) + Cc ≤ (Cc*(L:ℝ) + Cc) * (n:ℝ) := by
      nlinarith [mul_nonneg hnn (by linarith : (0:ℝ) ≤ (n:ℝ) - 1)]
    have s5 : (2*Cc + Cc*(L:ℝ) + Cc)*(n:ℝ) ≤ (Kc:ℝ)*(n:ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hKcR) (by linarith : (0:ℝ) ≤ (n:ℝ))]
    have s6 : ((Q.graph.dist o z : ℕ) : ℝ) ≤ ((Kc * n : ℕ) : ℝ) := by
      push_cast
      nlinarith [h1, s1, s3, s5]
    exact_mod_cast s6
  have hharmreg : ∀ (b : V) (γ : Q.graph.Walk b b), x₀ ∈ Q.embedding.cycleRegion γ →
      (∀ w ∈ γ.support, Q.graph.dist o w ≤ m + L) →
      ∀ z ∈ Q.embedding.cycleRegion γ, LatticeProb.Network.netLaplacian Q.graph c f z = 0 := by
    intro b γ _ hsupp z hz
    exact hharm z (mem_closedBall_of_dist Q.toPeriodicGraph o z (Kc*n) (hgeo b γ hsupp z hz))
  have hx₀m : Q.graph.dist o x₀ ≤ m := le_trans hx₀ hnm
  rcases hcase with ⟨hA, hB⟩ | hABlt
  · subst hA
    subst hB
    refine ⟨∅, by simp, ?_⟩
    have hzero := surroundedBy_zero_closed Q hES hU hL hc f o m (L+1) (le_refl _)
      hharmm hx₀m (by simpa using hfx₀) hharmreg
    simpa using hzero
  · have hx₀f : A < |f x₀| := lt_of_le_of_lt hAB hfx₀
    refine surroundedBy_band_closed Q hES hU hL hc f hABlt o m (L+1) (le_refl _)
      hharmm hx₀m hx₀f hharmreg ?_ ?_
    · intro b γ _ hsupp y hy hfy u hu hfu
      exact hupc hABlt y (hgeo b γ hsupp y hy) hfy u hu hfu
    · intro b γ _ hsupp y hy hfy u hu hfu
      exact hdnc hABlt y (hgeo b γ hsupp y hy) hfy u hu hfu

end UCPlanar.Support
