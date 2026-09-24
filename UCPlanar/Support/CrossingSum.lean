/- Finite summation over the crossing graph offsets. -/
import UCPlanar.Support.CrossingGraph
import Mathlib.Tactic
open scoped Classical BigOperators

theorem UCPlanar.Support.sum_eight (F : LatticeProb.Site 2 → ℝ) (x : LatticeProb.Site 2) :
    (∑ y ∈ ({x - LatticeProb.unit 0, x - LatticeProb.unit 1,
      x + LatticeProb.unit 0, x + LatticeProb.unit 1,
      x + (2 : ℤ) • UCPlanar.diagonalStep, x - (2 : ℤ) • UCPlanar.diagonalStep,
      x + UCPlanar.diagonalStep, x - UCPlanar.diagonalStep} : Finset (LatticeProb.Site 2)), F y) =
    F (x - LatticeProb.unit 0) + F (x - LatticeProb.unit 1) +
    F (x + LatticeProb.unit 0) + F (x + LatticeProb.unit 1) +
    F (x + (2 : ℤ) • UCPlanar.diagonalStep) + F (x - (2 : ℤ) • UCPlanar.diagonalStep) +
    F (x + UCPlanar.diagonalStep) + F (x - UCPlanar.diagonalStep)  := by
  have hne : ∀ (k l : LatticeProb.Site 2), k ≠ l → x + k ≠ x + l := by
    intro k l h
    exact fun hn => h (add_left_cancel hn)
  simp (disch := (simp_all [funext_iff, Fin.forall_fin_two, LatticeProb.unit,
    UCPlanar.diagonalStep]; omega)) only [Finset.sum_insert, Finset.sum_singleton]
  ring
