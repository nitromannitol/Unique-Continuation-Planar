module

/-
Assembly of the Liouville theorem from the uniform upper bound, the periodic
exponential lower bound, and the classical bounded-Liouville fact.
-/
public import UCPlanar.Basic
public import UCPlanar.Support.Periodic
public import UCPlanar.Support.Growth
public import UCPlanar.Support.LiouElliptic
public import UCPlanar.Support.LiouDensity
public import UCPlanar.Support.LiouCount
public import UCPlanar.Support.LiouTransfer
public import UCPlanar.Support.LiouDensityTransfer
public import UCPlanar.Support.LiouSupNorm
public import UCPlanar.Support.LiouSupBound
public import UCPlanar.Support.LiouEventually

@[expose] public section

open scoped Classical

namespace UCPlanar.Support

/-- The uniform upper bound of the paper's Theorem (uniformly-bounded), as a predicate
on a periodic plane graph. -/
def UniformUpperBound {V : Type*} (P : UCPlanar.PeriodicPlaneGraph V) : Prop :=
  ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ Θ : ℝ, 1 < Θ →
    ∃ ε₀ A : ℝ, 0 < ε₀ ∧ 0 < A ∧
    ∀ (lam : ℝ), 0 < lam → ∀ (c : V → V → ℝ),
    LatticeProb.Network.IsCond P.graph c → UCPlanar.UniformlyElliptic P.graph c lam (Θ*lam) →
    ∀ (o : V) (n : ℕ), n₀ ≤ n → ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ →
    ∀ f : V → ℝ,
      LatticeProb.Network.HarmonicOn P.graph c f (LatticeProb.Graph.closedBall P.graph o (2*n)) →
      (UCPlanar.exceptionalCount (P.toPeriodicGraph.ball o (2*n)) f 1 : ℝ) ≤
        ε * (P.toPeriodicGraph.ball o (2*n)).card →
      ∀ x ∈ P.toPeriodicGraph.ball o n, |f x| ≤ Real.exp (A * Real.sqrt ε * n)

/-- The periodic exponential lower bound of the paper's Theorem (lower-bound), as a
predicate on a periodic graph. -/
def PeriodicLowerBound {V : Type*} (P : UCPlanar.PeriodicGraph V) (c : V → V → ℝ) : Prop :=
  ∃ b : ℝ, 0 < b ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N₀ : ℕ, 0 < N₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ N : ℕ, N₀ ≤ N → ∀ f : V → ℝ,
      LatticeProb.Network.HarmonicOn P.graph c f Set.univ →
      (∃ x ∈ P.square (Nat.sqrt N), 2 ≤ f x) →
      (∀ K : ℕ, Real.sqrt N ≤ K → K ≤ 2*N →
        1 - ε ≤ UCPlanar.boundedDensity (P.square K) f 1) →
      Real.exp (b*N) ≤ UCPlanar.supNorm (P.square N) f

/-- The classical bounded-Liouville fact for a periodic network: a harmonic function
that is bounded on the whole graph is constant. -/
def BoundedLiouville {V : Type*} (P : UCPlanar.PeriodicGraph V) (c : V → V → ℝ) : Prop :=
  ∀ f : V → ℝ, LatticeProb.Network.HarmonicOn P.graph c f Set.univ →
    (∃ M : ℝ, ∀ x, |f x| ≤ M) → ∃ a : ℝ, ∀ x, f x = a

/-- The geometric comparison used by the assembly: every geometric square is contained
in a graph metric ball of linearly comparable radius. -/
def LinearSquareBall {V : Type*} (P : UCPlanar.PeriodicGraph V) (o : V) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 ≤ R → ∃ n : ℕ, (n : ℝ) ≤ C * (R + 1) ∧
    (P.square R : Set V) ⊆ (P.ball o n : Set V)

end UCPlanar.Support
