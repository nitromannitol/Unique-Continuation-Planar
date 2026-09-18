/-
Polynomial approximation on a translation orbit.
-/
import UCPlanar.Support.Periodic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval

/-- Membership in the lattice orbit of a vertex. -/
def UCPlanar.PeriodicGraph.OnOrbit {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (v x : V) : Prop :=
  ∃ k, P.shift k v = x

/-- Approximation by a polynomial of total degree at most `m` on an orbit. -/
def UCPlanar.PeriodicGraph.PolynomialApproximation {V : Type*}
    (P : UCPlanar.PeriodicGraph V) (R : ℝ) (m : ℕ) (v : V)
    (f : V → ℝ) (α c : ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin 2) ℝ, p.totalDegree ≤ m ∧
    ∀ x ∈ P.square (c * R), P.OnOrbit v x →
      |f x - MvPolynomial.eval (P.pos x) p| ≤ α ^ m * UCPlanar.supNorm (P.square (3 * R)) f
