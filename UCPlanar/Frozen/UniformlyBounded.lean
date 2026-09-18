import UCPlanar.Basic
import UCPlanar.Support.Periodic
import UCPlanar.Support.SurroundExists
import UCPlanar.Support.BandCoarse
import UCPlanar.External.EdgeSplitting
import UCPlanar.External.Unicoherence

-- FROZEN-STATEMENT-BEGIN
/-- “Then there exist positive constants ε₀, n₀, and A ... max on Bₙ |f| ≤ e^{A√ε n}.”
`ucplanar.tex:175-181 (theorem:uniformly-bounded)`.
The minimum radius depends only on geometry; ε₀ and A also depend on Λ/λ.  Step 1 repeats the
proof of the zero case and carries its two classical inputs about the plane, Janiszewski's
theorem at a point and unicoherence of the sphere, as hypotheses. -/
theorem UCPlanar.Frozen.uniformlyBounded {V : Type*} (P : UCPlanar.PeriodicPlaneGraph V)
    (hES : UCPlanar.External.EdgeSplitting P.embedding)
    (hU : UCPlanar.External.Unicoherence P.embedding) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ Θ : ℝ, 1 < Θ →
      ∃ ε₀ A : ℝ, 0 < ε₀ ∧ 0 < A ∧
      ∀ (lam : ℝ), 0 < lam → ∀ (c : V → V → ℝ),
      LatticeProb.Network.IsCond P.graph c → UCPlanar.UniformlyElliptic P.graph c lam (Θ*lam) →
      ∀ (o : V) (n : ℕ), n₀ ≤ n → ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ →
      ∀ f : V → ℝ,
        LatticeProb.Network.HarmonicOn P.graph c f (LatticeProb.Graph.closedBall P.graph o (2*n)) →
        (UCPlanar.exceptionalCount (P.toPeriodicGraph.ball o (2*n)) f 1 : ℝ) ≤
          ε * (P.toPeriodicGraph.ball o (2*n)).card →
        ∀ x ∈ P.toPeriodicGraph.ball o n, |f x| ≤ Real.exp (A * Real.sqrt ε * n)
-- FROZEN-STATEMENT-END
:= by
  obtain ⟨Kc, r, hK, hsur⟩ := UCPlanar.Support.exists_hasSurroundingCycles P hES hU
  exact UCPlanar.Support.uniformlyBounded_of_surrounding P Kc r hK hsur
