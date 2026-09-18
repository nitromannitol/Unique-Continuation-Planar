/-
Periodic networks have finitely many edge-conductance values.
-/
import UCPlanar.Support.Periodic

open scoped Classical

/-- The edge conductances of a periodic network take finitely many positive values. -/
theorem UCPlanar.Support.exists_edge_value_finset {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (c : V → V → ℝ) (hc : LatticeProb.Network.IsCond P.graph c)
    (hp : P.PeriodicConductance c) :
    ∃ T : Finset ℝ, (∀ x y, P.graph.Adj x y → c x y ∈ T) ∧ (∀ t ∈ T, 0 < t)
:= by
  refine ⟨P.representatives.biUnion (fun v => (P.graph.neighborFinset v).image (fun u => c v u)), ?_, ?_⟩
  · intro x y hxy
    obtain ⟨v, hv, a, ha⟩ := P.covers x
    subst ha
    have h2 : P.graph.Adj (P.shift (-a) (P.shift a v)) (P.shift (-a) y) :=
      (P.shift_adj (-a) (P.shift a v) y).mpr hxy
    simp only [← P.shift_add, neg_add_cancel, P.shift_zero] at h2
    refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
    refine Finset.mem_image.mpr ⟨P.shift (-a) y, (SimpleGraph.mem_neighborFinset _ _ _).mpr h2, ?_⟩
    have hper := hp a v (P.shift (-a) y)
    rw [← P.shift_add a (-a) y, add_neg_cancel, P.shift_zero] at hper
    exact hper.symm
  · intro t ht
    obtain ⟨v, hv, ht'⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht'
    exact hc.pos ((SimpleGraph.mem_neighborFinset _ _ _).mp hu)
