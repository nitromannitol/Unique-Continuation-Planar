import Mathlib
import UCPlanar.MainTheorems
import UCPlanarAudit.Counterexample.SolutionBasic
import UCPlanarAudit.Support.CounterexampleBridge

/-!
# Unconditional comparator solution: Counterexample

The theorem follows from the main result through the vocabulary bridge.
-/

namespace UCPlanarAudit

/-- Theorem 5.1 (`theorem:counterexample`). -/
theorem counterexample_unconditional (a b t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) (ht : 2*a^2*b^2 / ((a-b)^2*(a+b)) < t) :
    ∃ d : ℝ, 0 < d ∧ ∃ lf : crossingGraph.LocallyFinite,
      IsCond crossingGraph (crossingConductance a b t d) ∧
      ∃ f : Site 2 → ℝ,
        @HarmonicOn _ crossingGraph lf
          (crossingConductance a b t d) f Set.univ ∧
        f 0 = 1 ∧ ∀ x, f x ≠ 0 ↔ x 0 = x 1 := by
  obtain ⟨d, hd, lf, hc, f, hf⟩ := UCPlanar.counterexample a b t ha hb hab ht
  exact ⟨d, hd, lf, (Bridge.isCond_iff _ _).2 hc, f, hf⟩

end UCPlanarAudit
