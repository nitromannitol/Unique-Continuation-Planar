import UCPlanar.External.MoserEstimate
import UCPlanar.Support.LowerAssembly

-- FROZEN-STATEMENT-BEGIN
/-- “There is some b > 0 ... max on Qₙ |f| ≥ exp(bN).”
`ucplanar.tex:422-434,532-534 (theorem:lower-bound)`.
The periodic network form, with density at every integer scale from √N to 2N.
The proof runs the chain of three-ball inequalities and the discrete gradient estimate along one
lattice generator; the discrete Remez inequality is proved in `UCPlanar.Support.RemezDiscrete`,
and the discrete Moser estimate remains a hypothesis. -/
theorem UCPlanar.Frozen.periodicLowerBound {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (c : V → V → ℝ) (hc : LatticeProb.Network.IsCond P.graph c)
    (hp : P.PeriodicConductance c)
    (hMos : UCPlanar.External.MoserEstimate P c) :
    ∃ b : ℝ, 0 < b ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ N : ℕ, N₀ ≤ N → ∀ f : V → ℝ,
        LatticeProb.Network.HarmonicOn P.graph c f Set.univ →
        (∃ x ∈ P.square (Nat.sqrt N), 2 ≤ f x) →
        (∀ K : ℕ, Real.sqrt N ≤ K → K ≤ 2*N →
          1 - ε ≤ UCPlanar.boundedDensity (P.square K) f 1) →
        Real.exp (b*N) ≤ UCPlanar.supNorm (P.square N) f
-- FROZEN-STATEMENT-END
:= by
  exact UCPlanar.Support.Lower.periodicLowerBound_main P c hc hp hMos
