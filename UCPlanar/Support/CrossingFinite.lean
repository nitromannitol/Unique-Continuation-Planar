/- Local finiteness of the crossing graph of Section 5. -/
import UCPlanar.Support.CrossingGraph
import Mathlib.Tactic
open scoped Classical

noncomputable instance UCPlanar.crossingLocallyFinite : UCPlanar.crossingGraph.LocallyFinite := by
  intro x
  let S : Finset (LatticeProb.Site 2) :=
    {x - LatticeProb.unit 0, x - LatticeProb.unit 1,
     x + LatticeProb.unit 0, x + LatticeProb.unit 1,
     x + (2 : ℤ) • UCPlanar.diagonalStep, x - (2 : ℤ) • UCPlanar.diagonalStep,
     x + UCPlanar.diagonalStep, x - UCPlanar.diagonalStep}
  apply Set.Finite.fintype
  apply S.finite_toSet.subset
  intro y hy
  change UCPlanar.crossingGraph.Adj x y at hy
  change x ≠ y ∧ (UCPlanar.crossingRelation x y ∨ UCPlanar.crossingRelation y x) at hy
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton, S]
  rcases hy.2 with h | h
  · rcases h.2 with h | h | h | h | h | h | h | h
    · left
      exact h
    · right
      left
      exact h
    · right
      right
      left
      exact h
    · right
      right
      right
      left
      exact h
    · right
      right
      right
      right
      left
      exact h
    · right
      right
      right
      right
      right
      left
      exact h
    · right
      right
      right
      right
      right
      right
      left
      exact h
    · right
      right
      right
      right
      right
      right
      right
      exact h
  · rcases h.2 with h | h | h | h | h | h | h | h
    · right
      right
      left
      rw [h]
      abel
    · right
      right
      right
      left
      rw [h]
      abel
    · left
      rw [h]
      abel
    · right
      left
      rw [h]
      abel
    · right
      right
      right
      right
      right
      left
      rw [h]
      abel
    · right
      right
      right
      right
      left
      rw [h]
      abel
    · right
      right
      right
      right
      right
      right
      right
      rw [h]
      abel
    · right
      right
      right
      right
      right
      right
      left
      rw [h]
      abel
