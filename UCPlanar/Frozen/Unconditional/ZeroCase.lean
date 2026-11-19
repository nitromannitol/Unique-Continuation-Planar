import UCPlanar.Proved.MoserEstimate

/-! # Unconditional form of the continuation theorem -/

-- FROZEN-STATEMENT-BEGIN
theorem UCPlanar.Frozen.zeroCase_unconditional {V : Type*} (P : UCPlanar.PeriodicPlaneGraph V) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (c : V → V → ℝ), LatticeProb.Network.IsCond P.graph c →
      ∀ (o : V) (n : ℕ), n₀ ≤ n → ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ →
      ∀ f : V → ℝ,
        LatticeProb.Network.HarmonicOn P.graph c f (LatticeProb.Graph.closedBall P.graph o (2*n)) →
        (UCPlanar.exceptionalCount (P.toPeriodicGraph.ball o (2*n)) f 0 : ℝ) ≤
          ε * (P.toPeriodicGraph.ball o (2*n)).card →
        ∀ x ∈ P.toPeriodicGraph.ball o n, f x = 0
-- FROZEN-STATEMENT-END
:= UCPlanar.Proved.zeroCase P
