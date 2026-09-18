/- The observation that opens Section 4: under uniform ellipticity a small value with a large
neighbour has a large neighbour of the opposite sign. -/
import UCPlanar.Support.ZeroAssemble
import Mathlib

open scoped BigOperators Classical

namespace UCPlanar.Support

/-- **The observation that opens Section 4.**  Under uniform ellipticity, a vertex where the
harmonic function is at most `A` in absolute value and which has a neighbour at least
`(2 Θ d + 2) A` has a neighbour below `-A`. -/
theorem band_exists_opposite_neighbor {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    {c : V → V → ℝ} {f : V → ℝ} (d : ℕ) (hd : ∀ x, G.degree x ≤ d)
    (lam Θ : ℝ) (hlam : 0 < lam) (hΘ : 1 < Θ)
    (hell : UCPlanar.UniformlyElliptic G c lam (Θ*lam))
    (A : ℝ) (hA : 0 < A) {z : V}
    (hz : LatticeProb.Network.netLaplacian G c f z = 0) (hfz : |f z| ≤ A)
    {w : V} (hw : G.Adj z w) (hfw : (2*Θ*d + 2) * A ≤ f w) :
    ∃ y, G.Adj z y ∧ f y < -A := by
  classical
  have hmean : ∑ i ∈ G.neighborFinset z, c z i * (f i - f z) = 0 := by
    rw [← LatticeProb.Network.netLaplacian]; exact hz
  have hcbound : ∀ i ∈ G.neighborFinset z, lam ≤ c z i ∧ c z i ≤ Θ*lam := by
    intro i hi
    have ha := (SimpleGraph.mem_neighborFinset G z i).mp hi
    obtain ⟨h1, h2⟩ := hell.2.2 z i ha
    exact ⟨h1.le, h2.le⟩
  have hcard : ((G.neighborFinset z).card : ℝ) ≤ (d : ℝ) := by
    have := hd z
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact_mod_cast this
  have hfzle : f z ≤ A := le_trans (le_abs_self _) hfz
  have hlarge : Θ*lam * ((G.neighborFinset z).card : ℝ) * (2*A) < lam * (f w - f z) := by
    have hd0 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg _
    have hpos : (0:ℝ) ≤ Θ*lam := by nlinarith
    have h1 : Θ*lam * ((G.neighborFinset z).card : ℝ) * (2*A) ≤ Θ*lam*(d:ℝ)*(2*A) := by
      have hmul : Θ*lam * ((G.neighborFinset z).card : ℝ) ≤ Θ*lam*(d:ℝ) :=
        mul_le_mul_of_nonneg_left hcard hpos
      have h2A : (0:ℝ) ≤ 2*A := by linarith
      exact mul_le_mul_of_nonneg_right hmul h2A
    have hstep : (2*Θ*(d:ℝ) + 2) * A - A ≤ f w - f z := by linarith
    have h2 : lam * ((2*Θ*(d:ℝ) + 2) * A - A) ≤ lam * (f w - f z) :=
      mul_le_mul_of_nonneg_left hstep hlam.le
    have h3 : Θ*lam*(d:ℝ)*(2*A) < lam * ((2*Θ*(d:ℝ) + 2) * A - A) := by
      nlinarith [mul_pos hlam hA]
    linarith [h1, h2, h3]
  obtain ⟨j, hj, hjlt⟩ := UCPlanar.Support.band_opposite (G.neighborFinset z)
    (fun i => c z i) (fun i => f i - f z) (2*A) lam (Θ*lam) (by linarith) hlam
    (by nlinarith) hcbound hmean w ((SimpleGraph.mem_neighborFinset G z w).mpr hw) hlarge
  refine ⟨j, (SimpleGraph.mem_neighborFinset G z j).mp hj, ?_⟩
  have hjlt' : f j - f z < -(2*A) := hjlt
  linarith

/-- **The opposite sign, downwards.**  The companion of `band_exists_opposite_neighbor` for a
neighbour far below `-A`, obtained by applying it to the negative of the function. -/
theorem band_exists_opposite_neighbor' {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    {c : V → V → ℝ} {f : V → ℝ} (d : ℕ) (hd : ∀ x, G.degree x ≤ d)
    (lam Θ : ℝ) (hlam : 0 < lam) (hΘ : 1 < Θ)
    (hell : UCPlanar.UniformlyElliptic G c lam (Θ*lam))
    (A : ℝ) (hA : 0 < A) {z : V}
    (hz : LatticeProb.Network.netLaplacian G c f z = 0) (hfz : |f z| ≤ A)
    {w : V} (hw : G.Adj z w) (hfw : f w ≤ -((2*Θ*d + 2) * A)) :
    ∃ y, G.Adj z y ∧ A < f y := by
  classical
  have hneg : LatticeProb.Network.netLaplacian G c (fun v => - f v) z = 0 := by
    rw [netLaplacian_neg, hz]; ring
  have hfzn : |(fun v => - f v) z| ≤ A := by simpa using hfz
  have hfwn : (2*Θ*(d:ℝ) + 2) * A ≤ (fun v => - f v) w := by
    show (2*Θ*(d:ℝ) + 2) * A ≤ - f w
    linarith
  obtain ⟨y, hy1, hy2⟩ :=
    band_exists_opposite_neighbor (f := fun v => - f v) d hd lam Θ hlam hΘ hell A hA
      hneg hfzn hw hfwn
  refine ⟨y, hy1, ?_⟩
  have : - f y < -A := hy2
  linarith

end UCPlanar.Support
