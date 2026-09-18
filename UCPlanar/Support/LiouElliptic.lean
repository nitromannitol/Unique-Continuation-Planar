/-
Periodic positive conductances give a global ellipticity ratio.
-/
import UCPlanar.Support.LiouEllipticValue
import UCPlanar.Basic

open scoped Classical

/-- A periodic positive conductance is uniformly elliptic for some pair of constants. -/
theorem UCPlanar.Support.uniformlyElliptic_of_periodic {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (c : V → V → ℝ) (hc : LatticeProb.Network.IsCond P.graph c)
    (hp : P.PeriodicConductance c) :
    ∃ lam big : ℝ, UCPlanar.UniformlyElliptic P.graph c lam big
:= by
  obtain ⟨T, hT, hpos⟩ := UCPlanar.Support.exists_edge_value_finset P c hc hp
  by_cases hne : T.Nonempty
  · refine ⟨T.min' hne / 2, 2 * T.max' hne, ?_, ?_, ?_⟩
    · have h1 := hpos _ (Finset.min'_mem T hne)
      linarith
    · have h1 := hpos _ (Finset.min'_mem T hne)
      have h2 := hpos _ (Finset.max'_mem T hne)
      have h3 : T.min' hne ≤ T.max' hne := Finset.min'_le T _ (Finset.max'_mem T hne)
      linarith
    · intro x y hxy
      have hcxy := hT x y hxy
      have h1 := hpos _ (Finset.min'_mem T hne)
      have h2 := hpos _ (Finset.max'_mem T hne)
      have h3 : T.min' hne ≤ c x y := Finset.min'_le T _ hcxy
      have h4 : c x y ≤ T.max' hne := Finset.le_max' T _ hcxy
      exact ⟨by linarith, by linarith⟩
  · refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
    intro x y hxy
    have hmem := hT x y hxy
    rw [Finset.not_nonempty_iff_eq_empty.mp hne] at hmem
    exact absurd hmem (by simp)
