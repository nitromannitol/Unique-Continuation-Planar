import Mathlib
import UCPlanar.MainTheorems
import UCPlanarAudit.UniformlyBounded.SolutionBasic
import UCPlanarAudit.Support.UniformlyBoundedBridge

/-!
# Solution: UniformlyBounded

The challenge module `UCPlanarAudit/UniformlyBounded/Challenge.lean` imports only Mathlib and
states the theorem with one intentional `sorry`.  This solution imports the repository together
with `UCPlanarAudit.UniformlyBounded.SolutionBasic`, a verbatim copy of the challenge's
vocabulary, and proves the byte-identical statement from `UCPlanar.uniformlyBounded` through the
bridge in `UCPlanarAudit/Support/UniformlyBoundedBridge.lean`.
-/

namespace UCPlanarAudit

/-- Theorem 1.2 (`theorem:uniformly-bounded`). -/
theorem uniformlyBounded {V : Type*} (P : PeriodicPlaneGraph V)
    (hES : External.EdgeSplitting P.embedding)
    (hU : External.Unicoherence P.embedding) :
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
  obtain ⟨n₀, hn₀, h⟩ := UCPlanar.uniformlyBounded (Bridge.toPPG P)
    (Bridge.edgeSplitting _ hES) (Bridge.unicoherence _ hU)
  refine ⟨n₀, hn₀, fun Θ hΘ => ?_⟩
  obtain ⟨ε₀, A, hε₀, hA, h'⟩ := h Θ hΘ
  exact ⟨ε₀, A, hε₀, hA, fun lam hlam c hc => h' lam hlam c ((Bridge.isCond_iff _ _).1 hc)⟩

end UCPlanarAudit
