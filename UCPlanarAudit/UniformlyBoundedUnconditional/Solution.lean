import UCPlanar.Proved.MoserEstimate
import Mathlib
import UCPlanar.MainTheorems
import UCPlanarAudit.UniformlyBounded.SolutionBasic
import UCPlanarAudit.Support.UniformlyBoundedBridge

/-!
# Unconditional comparator solution: UniformlyBounded

The theorem follows from the unconditional result through the vocabulary bridge.
-/

namespace UCPlanarAudit

/-- Theorem 1.2 (`theorem:uniformly-bounded`). -/
theorem uniformlyBounded_unconditional {V : Type*} (P : PeriodicPlaneGraph V)
    :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ Θ : ℝ, 1 < Θ →
      ∃ ε₀ A : ℝ, 0 < ε₀ ∧ 0 < A ∧
      ∀ (lam : ℝ), 0 < lam → ∀ (c : V → V → ℝ),
      IsCond P.graph c → UniformlyElliptic P.graph c lam (Θ*lam) →
      ∀ (o : V) (n : ℕ), n₀ ≤ n → ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ →
      ∀ f : V → ℝ,
        HarmonicOn P.graph c f (closedBall P.graph o (2*n)) →
        (exceptionalCount (P.toPeriodicGraph.ball o (2*n)) f 1 : ℝ) ≤
          ε * (P.toPeriodicGraph.ball o (2*n)).card →
        ∀ x ∈ P.toPeriodicGraph.ball o n, |f x| ≤ Real.exp (A * Real.sqrt ε * n) := by
  obtain ⟨n₀, hn₀, h⟩ := UCPlanar.Proved.uniformlyBounded (Bridge.toPPG P)
  refine ⟨n₀, hn₀, fun Θ hΘ => ?_⟩
  obtain ⟨ε₀, A, hε₀, hA, h'⟩ := h Θ hΘ
  exact ⟨ε₀, A, hε₀, hA, fun lam hlam c hc => h' lam hlam c ((Bridge.isCond_iff _ _).1 hc)⟩

end UCPlanarAudit
