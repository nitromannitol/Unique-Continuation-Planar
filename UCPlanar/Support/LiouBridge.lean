/-
The frozen statements of the uniform upper bound and the periodic lower bound
instantiate the assembly predicates.
-/
import UCPlanar.Support.LiouMain
import UCPlanar.Frozen.UniformlyBounded
import UCPlanar.Frozen.PeriodicLowerBound

open scoped Classical

namespace UCPlanar.Support

/-- The frozen uniform upper bound is the assembly predicate. -/
theorem uniformUpperBound_of_frozen {V : Type*} (P : UCPlanar.PeriodicPlaneGraph V)
    (h : ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ Θ : ℝ, 1 < Θ →
      ∃ ε₀ A : ℝ, 0 < ε₀ ∧ 0 < A ∧
      ∀ (lam : ℝ), 0 < lam → ∀ (c : V → V → ℝ),
      LatticeProb.Network.IsCond P.graph c → UCPlanar.UniformlyElliptic P.graph c lam (Θ*lam) →
      ∀ (o : V) (n : ℕ), n₀ ≤ n → ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ →
      ∀ f : V → ℝ,
        LatticeProb.Network.HarmonicOn P.graph c f (LatticeProb.Graph.closedBall P.graph o (2*n)) →
        (UCPlanar.exceptionalCount (P.toPeriodicGraph.ball o (2*n)) f 1 : ℝ) ≤
          ε * (P.toPeriodicGraph.ball o (2*n)).card →
        ∀ x ∈ P.toPeriodicGraph.ball o n, |f x| ≤ Real.exp (A * Real.sqrt ε * n)) :
    UniformUpperBound P := h

/-- The frozen periodic lower bound is the assembly predicate. -/
theorem periodicLowerBound_of_frozen {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (c : V → V → ℝ)
    (h : ∃ b : ℝ, 0 < b ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ N : ℕ, N₀ ≤ N → ∀ f : V → ℝ,
        LatticeProb.Network.HarmonicOn P.graph c f Set.univ →
        (∃ x ∈ P.square (Nat.sqrt N), 2 ≤ f x) →
        (∀ K : ℕ, Real.sqrt N ≤ K → K ≤ 2*N →
          1 - ε ≤ UCPlanar.boundedDensity (P.square K) f 1) →
        Real.exp (b*N) ≤ UCPlanar.supNorm (P.square N) f) :
    PeriodicLowerBound P c := h

end UCPlanar.Support
