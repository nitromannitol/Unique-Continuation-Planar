import UCPlanar.Proved.MoserEstimate
import Mathlib
import UCPlanar.MainTheorems
import UCPlanarAudit.ZeroCase.SolutionBasic
import UCPlanarAudit.Support.ZeroCaseBridge

/-!
# Unconditional comparator solution: ZeroCase

The theorem follows from the unconditional result through the vocabulary bridge.
-/

namespace UCPlanarAudit

/-- Theorem 1.3 (`theorem:zero-case`). -/
theorem zeroCase_unconditional {V : Type*} (P : PeriodicPlaneGraph V)
    :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (c : V → V → ℝ), IsCond P.graph c →
      ∀ (o : V) (n : ℕ), n₀ ≤ n → ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ →
      ∀ f : V → ℝ,
        HarmonicOn P.graph c f (closedBall P.graph o (2*n)) →
        (exceptionalCount (P.toPeriodicGraph.ball o (2*n)) f 0 : ℝ) ≤
          ε * (P.toPeriodicGraph.ball o (2*n)).card →
        ∀ x ∈ P.toPeriodicGraph.ball o n, f x = 0 := by
  obtain ⟨ε₀, hε₀, n₀, hn₀, h⟩ := UCPlanar.Proved.zeroCase (Bridge.toPPG P)
  exact ⟨ε₀, hε₀, n₀, hn₀, fun c hc => h c ((Bridge.isCond_iff _ _).1 hc)⟩

end UCPlanarAudit
