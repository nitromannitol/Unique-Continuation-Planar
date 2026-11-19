import UCPlanar.Proved.MoserEstimate

/-! # Unconditional form of the continuation theorem -/

-- FROZEN-STATEMENT-BEGIN
theorem UCPlanar.Frozen.threeBall_unconditional {V : Type*} (P : UCPlanar.PeriodicGraph V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ c : V → V → ℝ,
      LatticeProb.Network.IsCond P.graph c → P.PeriodicConductance c →
      ∃ (k : ℕ) (c₀ C : ℝ), 4 ≤ k ∧ 0 < c₀ ∧ 0 < C ∧
      ∀ N : ℕ, 0 < N → ∀ (f : V → ℝ) (M : ℝ), 0 ≤ M →
        LatticeProb.Network.HarmonicOn P.graph c f (P.square (k*N) : Set V) →
        1 - ε ≤ UCPlanar.boundedDensity (P.square N) f 1 →
        (∀ x ∈ P.square (k*N), |f x| ≤ M) →
        ∀ x ∈ P.square (2*N), |f x| ≤ C*Real.sqrt M + C*Real.exp (-c₀*N)*M
-- FROZEN-STATEMENT-END
:= UCPlanar.Proved.threeBall P
