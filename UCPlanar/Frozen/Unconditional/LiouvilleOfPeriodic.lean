import UCPlanar.Proved.MoserEstimate

/-! # Unconditional form of the continuation theorem -/

-- FROZEN-STATEMENT-BEGIN
theorem UCPlanar.Frozen.liouville_of_periodic {V : Type*} (P : UCPlanar.PeriodicPlaneGraph V)
    (c : V → V → ℝ) (hc : LatticeProb.Network.IsCond P.graph c)
    (hp : P.toPeriodicGraph.PeriodicConductance c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (o : V) (f : V → ℝ),
      LatticeProb.Network.HarmonicOn P.graph c f Set.univ →
      P.toPeriodicGraph.HasBoundedDensity o f ε → ∃ a : ℝ, ∀ x, f x = a
-- FROZEN-STATEMENT-END
:= UCPlanar.Proved.liouville_of_periodic P c hc hp
