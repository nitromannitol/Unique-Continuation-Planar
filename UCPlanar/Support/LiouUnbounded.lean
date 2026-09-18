/-
A nonconstant harmonic function is unbounded, by the classical bounded-Liouville fact.
-/
import UCPlanar.Support.LiouAssembly

open scoped Classical

namespace UCPlanar.Support

/-- Contrapositive of the classical bounded-Liouville fact: a harmonic function that is
not constant is unbounded. -/
theorem not_bounded_of_not_constant {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (c : V → V → ℝ) (hBL : BoundedLiouville P c) (f : V → ℝ)
    (hf : LatticeProb.Network.HarmonicOn P.graph c f Set.univ)
    (hnc : ∀ a : ℝ, ∃ x, f x ≠ a) :
    ∀ M : ℝ, ∃ x, M < |f x| := by
  intro M
  by_contra h
  push Not at h
  obtain ⟨a, ha⟩ := hBL f hf ⟨M, h⟩
  obtain ⟨x, hx⟩ := hnc a
  exact absurd (ha x) hx

end UCPlanar.Support
