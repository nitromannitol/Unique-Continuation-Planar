import Mathlib
import Audit.Support.Vocabulary

/-!
# The audited statements in the challenge environment

Each audited statement, elaborated as a proposition in exactly the environment
of the challenges: this module imports only Mathlib and the vocabulary.
`Audit/StatementRegression.lean` checks that each solution theorem has
exactly this type, so that no repository name or instance leaks into a
solution statement.
-/

namespace UCPlanarAudit.Statements

open UCPlanarAudit

-- The hypothesis names are kept so that the text matches the challenges.
set_option linter.unusedVariables false

/-- The statement of `Audit/Liouville/Challenge.lean`. -/
def liouville : Prop :=
  ∀ {V : Type*} (P : PeriodicPlaneGraph V)
    (c : V → V → ℝ) (hc : IsCond P.graph c)
    (hp : P.toPeriodicGraph.PeriodicConductance c)
    (hMos : External.MoserEstimate P.toPeriodicGraph c)
    (hES : External.EdgeSplitting P.embedding)
    (hU : External.Unicoherence P.embedding),
    ∃ ε : ℝ, 0 < ε ∧ ∀ (o : V) (f : V → ℝ),
      HarmonicOn P.graph c f Set.univ →
      P.toPeriodicGraph.HasBoundedDensity o f ε → ∃ a : ℝ, ∀ x, f x = a

/-- The statement of `Audit/UniformlyBounded/Challenge.lean`. -/
def uniformlyBounded : Prop :=
  ∀ {V : Type*} (P : PeriodicPlaneGraph V)
    (hES : External.EdgeSplitting P.embedding)
    (hU : External.Unicoherence P.embedding),
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ Θ : ℝ, 1 < Θ →
      ∃ ε₀ A : ℝ, 0 < ε₀ ∧ 0 < A ∧
      ∀ (lam : ℝ), 0 < lam → ∀ (c : V → V → ℝ),
      IsCond P.graph c → UniformlyElliptic P.graph c lam (Θ*lam) →
      ∀ (o : V) (n : ℕ), n₀ ≤ n → ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ →
      ∀ f : V → ℝ,
        HarmonicOn P.graph c f (closedBall P.graph o (2*n)) →
        (exceptionalCount (P.toPeriodicGraph.ball o (2*n)) f 1 : ℝ) ≤
          ε * (P.toPeriodicGraph.ball o (2*n)).card →
        ∀ x ∈ P.toPeriodicGraph.ball o n, |f x| ≤ Real.exp (A * Real.sqrt ε * n)

/-- The statement of `Audit/ZeroCase/Challenge.lean`. -/
def zeroCase : Prop :=
  ∀ {V : Type*} (P : PeriodicPlaneGraph V)
    (hES : External.EdgeSplitting P.embedding)
    (hU : External.Unicoherence P.embedding),
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (c : V → V → ℝ), IsCond P.graph c →
      ∀ (o : V) (n : ℕ), n₀ ≤ n → ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ →
      ∀ f : V → ℝ,
        HarmonicOn P.graph c f (closedBall P.graph o (2*n)) →
        (exceptionalCount (P.toPeriodicGraph.ball o (2*n)) f 0 : ℝ) ≤
          ε * (P.toPeriodicGraph.ball o (2*n)).card →
        ∀ x ∈ P.toPeriodicGraph.ball o n, f x = 0

/-- The statement of `Audit/Counterexample/Challenge.lean`. -/
def counterexample : Prop :=
  ∀ (a b t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) (ht : 2*a^2*b^2 / ((a-b)^2*(a+b)) < t),
    ∃ d : ℝ, 0 < d ∧ ∃ lf : crossingGraph.LocallyFinite,
      IsCond crossingGraph (crossingConductance a b t d) ∧
      ∃ f : Site 2 → ℝ,
        @HarmonicOn _ crossingGraph lf
          (crossingConductance a b t d) f Set.univ ∧
        f 0 = 1 ∧ ∀ x, f x ≠ 0 ↔ x 0 = x 1

end UCPlanarAudit.Statements
