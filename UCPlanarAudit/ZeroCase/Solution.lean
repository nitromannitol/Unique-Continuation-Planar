import Mathlib
import UCPlanar.MainTheorems
import UCPlanarAudit.ZeroCase.SolutionBasic
import UCPlanarAudit.Support.ZeroCaseBridge

/-!
# Solution: ZeroCase

The challenge module `UCPlanarAudit/ZeroCase/Challenge.lean` imports only Mathlib and states the
theorem with one intentional `sorry`.  This solution imports the repository together with
`UCPlanarAudit.ZeroCase.SolutionBasic`, a verbatim copy of the challenge's vocabulary, and
proves the byte-identical statement from `UCPlanar.zeroCase` through the bridge in
`UCPlanarAudit/Support/ZeroCaseBridge.lean`.
-/

namespace UCPlanarAudit

/-- Theorem 1.3 (`theorem:zero-case`). -/
theorem zeroCase {V : Type*} (P : PeriodicPlaneGraph V)
    (hES : External.EdgeSplitting P.embedding)
    (hU : External.Unicoherence P.embedding) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (c : V → V → ℝ), IsCond P.graph c →
      ∀ (o : V) (n : ℕ), n₀ ≤ n → ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ →
      ∀ f : V → ℝ,
        HarmonicOn P.graph c f (closedBall P.graph o (2*n)) →
        (exceptionalCount (P.toPeriodicGraph.ball o (2*n)) f 0 : ℝ) ≤
          ε * (P.toPeriodicGraph.ball o (2*n)).card →
        ∀ x ∈ P.toPeriodicGraph.ball o n, f x = 0 := by
  obtain ⟨ε₀, hε₀, n₀, hn₀, h⟩ := UCPlanar.zeroCase (Bridge.toPPG P)
    (Bridge.edgeSplitting _ hES) (Bridge.unicoherence _ hU)
  exact ⟨ε₀, hε₀, n₀, hn₀, fun c hc => h c ((Bridge.isCond_iff _ _).1 hc)⟩

end UCPlanarAudit
