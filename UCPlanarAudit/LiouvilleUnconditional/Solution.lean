import UCPlanar.Proved.MoserEstimate
import Mathlib
import UCPlanar.MainTheorems
import UCPlanarAudit.Liouville.SolutionBasic
import UCPlanarAudit.Support.LiouvilleBridge

/-!
# Unconditional comparator solution: Liouville

The theorem follows from the unconditional result through the vocabulary bridge.
-/

namespace UCPlanarAudit

/-- Theorem 1.1 (`theorem:liouville`). -/
theorem liouville_unconditional {V : Type*} (P : PeriodicPlaneGraph V)
    (c : V → V → ℝ) (hc : IsCond P.graph c)
    (hp : P.toPeriodicGraph.PeriodicConductance c)
    :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (o : V) (f : V → ℝ),
      HarmonicOn P.graph c f Set.univ →
      P.toPeriodicGraph.HasBoundedDensity o f ε → ∃ a : ℝ, ∀ x, f x = a := by
  exact UCPlanar.Proved.liouville_of_periodic (Bridge.toPPG P) c ((Bridge.isCond_iff _ _).1 hc) hp

end UCPlanarAudit
