import UCPlanar.Proved.MoserEstimate

/-! # Unconditional form of the continuation theorem -/

-- FROZEN-STATEMENT-BEGIN
theorem UCPlanar.Frozen.polynomialApproximation_unconditional {V : Type*}
    (P : UCPlanar.PeriodicGraph V) (c : V → V → ℝ)
    (hc : LatticeProb.Network.IsCond P.graph c) (hp : P.PeriodicConductance c) :
    ∀ α : ℝ, 0 < α → ∃ δ R₀ : ℝ, 0 < δ ∧ 0 < R₀ ∧
      ∀ R : ℝ, R₀ ≤ R → ∀ m : ℕ, (m : ℝ) ≤ δ*R →
      ∀ (v : V) (f : V → ℝ),
        LatticeProb.Network.HarmonicOn P.graph c f (P.square (3*R) : Set V) →
        P.PolynomialApproximation R m v f α δ
-- FROZEN-STATEMENT-END
:= UCPlanar.Proved.polynomialApproximation P c hc hp
