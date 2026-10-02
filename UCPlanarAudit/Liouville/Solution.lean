import Mathlib
import UCPlanar.MainTheorems
import UCPlanarAudit.Liouville.SolutionBasic
import UCPlanarAudit.Support.LiouvilleBridge

/-!
# Solution: Liouville

The challenge module `UCPlanarAudit/Liouville/Challenge.lean` imports only Mathlib and states
the theorem with one intentional `sorry`.  This solution imports the repository together with
`UCPlanarAudit.Liouville.SolutionBasic`, a verbatim copy of the challenge's vocabulary, and
proves the byte-identical statement from `UCPlanar.liouville` through the bridge in
`UCPlanarAudit/Support/LiouvilleBridge.lean`.
-/

namespace UCPlanarAudit

/-- Theorem 1.1 (`theorem:liouville`). -/
theorem liouville {V : Type*} (P : PeriodicPlaneGraph V)
    (c : V → V → ℝ) (hc : IsCond P.graph c)
    (hp : P.toPeriodicGraph.PeriodicConductance c)
    (hMos : External.MoserEstimate P.toPeriodicGraph c)
    (hES : External.EdgeSplitting P.embedding)
    (hU : External.Unicoherence P.embedding) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (o : V) (f : V → ℝ),
      HarmonicOn P.graph c f Set.univ →
      P.toPeriodicGraph.HasBoundedDensity o f ε → ∃ a : ℝ, ∀ x, f x = a := by
  exact UCPlanar.liouville (Bridge.toPPG P) c ((Bridge.isCond_iff _ _).1 hc) hp
    (Bridge.moserEstimate _ c hMos) (Bridge.edgeSplitting _ hES) (Bridge.unicoherence _ hU)

end UCPlanarAudit
