import UCPlanar.Basic
import UCPlanar.Support.Periodic
import UCPlanar.Support.SurroundExists
import UCPlanar.External.EdgeSplitting
import UCPlanar.External.Unicoherence

-- FROZEN-STATEMENT-BEGIN
/-- “There exist positive constants ε₀ and n₀ ... then f ≡ 0 on Bₙ.”
`ucplanar.tex:187-190 (theorem:zero-case)`.
Both constants depend only on the periodic plane graph.  The proof of Step 3 uses two
classical inputs about the plane, carried here as hypotheses: Janiszewski's theorem at a point,
which turns a separating finite edge set into a separating cycle, and unicoherence of the
sphere, which makes the frontier of a bounded face connected. -/
theorem UCPlanar.Frozen.zeroCase {V : Type*} (P : UCPlanar.PeriodicPlaneGraph V)
    (hES : UCPlanar.External.EdgeSplitting P.embedding)
    (hU : UCPlanar.External.Unicoherence P.embedding) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (c : V → V → ℝ), LatticeProb.Network.IsCond P.graph c →
      ∀ (o : V) (n : ℕ), n₀ ≤ n → ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ →
      ∀ f : V → ℝ,
        LatticeProb.Network.HarmonicOn P.graph c f (LatticeProb.Graph.closedBall P.graph o (2*n)) →
        (UCPlanar.exceptionalCount (P.toPeriodicGraph.ball o (2*n)) f 0 : ℝ) ≤
          ε * (P.toPeriodicGraph.ball o (2*n)).card →
        ∀ x ∈ P.toPeriodicGraph.ball o n, f x = 0
-- FROZEN-STATEMENT-END
:= by
  obtain ⟨Kc, r, hK, hsur⟩ := UCPlanar.Support.exists_hasSurroundingCycles P hES hU
  exact UCPlanar.Support.zeroCase_of_surrounding P Kc r hK hsur
