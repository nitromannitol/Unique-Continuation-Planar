import Mathlib
import UCPlanar.MainTheorems
import UCPlanarAudit.Counterexample.SolutionBasic

/-!
# Bridge from the `Counterexample` vocabulary to the repository

The vocabulary of `UCPlanarAudit/Counterexample/Challenge.lean` (copied verbatim into
`UCPlanarAudit/Counterexample/SolutionBasic.lean`, which imports only Mathlib; namespace
`UCPlanarAudit`) is a statement-level copy of the repository definitions and of the definitions
it uses from `Lattice-Probability`.  Plain definitions over shared Mathlib types
(`closedBall`, `netLaplacian`, `HarmonicOn`, `crossingGraph`, `crossingConductance`, …) are
definitionally equal to their counterparts.  The one structure the theorem mentions, `IsCond`,
is a new inductive type, so this file converts between the two copies field by field.

It is imported by `UCPlanarAudit/Counterexample/Solution.lean` only.  The `Challenge` and
`SolutionBasic` files must stay Mathlib-only: a repository import inside the vocabulary
changes instance elaboration there and breaks the comparator's constant-by-constant closure
check.
-/

namespace UCPlanarAudit.Bridge

section Graph

variable {V : Type*}

theorem isCond_iff (G : SimpleGraph V) (c : V → V → ℝ) :
    UCPlanarAudit.IsCond G c ↔ LatticeProb.Network.IsCond G c :=
  ⟨fun h => ⟨h.symm, h.pos, h.zero_of_not_adj⟩, fun h => ⟨h.symm, h.pos, h.zero_of_not_adj⟩⟩

end Graph

end UCPlanarAudit.Bridge
