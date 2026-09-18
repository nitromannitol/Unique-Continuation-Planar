/-
Density limits and exponential growth in graph metric balls.
-/
import UCPlanar.Basic
import UCPlanar.Support.Periodic

/-- Existence of the bounded-value density limit, with its lower bound. -/
def UCPlanar.PeriodicGraph.HasBoundedDensity {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (o : V) (f : V → ℝ) (ε : ℝ) : Prop :=
  ∃ d : ℝ, 1 - ε ≤ d ∧ Filter.Tendsto
    (fun n : ℕ => UCPlanar.boundedDensity (P.ball o n) f 1) Filter.atTop (nhds d)

/-- An eventual exponential bound on the graph metric balls. -/
def UCPlanar.PeriodicGraph.ExponentialBound {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (o : V) (f : V → ℝ) (A : ℝ) : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, ∀ x ∈ P.ball o n, |f x| ≤ Real.exp (A * n)
