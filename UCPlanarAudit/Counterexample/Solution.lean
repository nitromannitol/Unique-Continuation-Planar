import Mathlib
import UCPlanar.MainTheorems
import UCPlanarAudit.Counterexample.SolutionBasic
import UCPlanarAudit.Support.CounterexampleBridge

/-!
# Solution: Counterexample

The challenge module `UCPlanarAudit/Counterexample/Challenge.lean` imports only Mathlib and
states the theorem with one intentional `sorry`.  This solution imports the repository together
with `UCPlanarAudit.Counterexample.SolutionBasic`, a verbatim copy of the challenge's
vocabulary, and proves the byte-identical statement from `UCPlanar.counterexample` through the
bridge in `UCPlanarAudit/Support/CounterexampleBridge.lean`.
-/

namespace UCPlanarAudit

/-- Theorem 5.1 (`theorem:counterexample`). -/
theorem counterexample (a b t : ℝ) (ha : 0 < a) (hb : 0 < b)
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
