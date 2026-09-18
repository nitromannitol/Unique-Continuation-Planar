/-
A periodic positive conductance has a finite ellipticity ratio.
-/
import UCPlanar.Support.LiouElliptic

open scoped Classical
set_option autoImplicit false

namespace UCPlanar.Support

/-- **A periodic positive conductance is uniformly elliptic with a ratio above one.**  The
conductance takes finitely many values on the edges, so the quotient of the largest by the
smallest is a finite number bigger than one. -/
theorem uniformlyElliptic_ratio {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (c : V → V → ℝ) (hc : LatticeProb.Network.IsCond P.graph c)
    (hp : P.PeriodicConductance c) :
    ∃ lam Θ : ℝ, 0 < lam ∧ 1 < Θ ∧ UCPlanar.UniformlyElliptic P.graph c lam (Θ*lam) := by
  obtain ⟨lam, big, hlam, hlb, hall⟩ := UCPlanar.Support.uniformlyElliptic_of_periodic P c hc hp
  refine ⟨lam, big / lam, hlam, (one_lt_div hlam).mpr hlb, ?_⟩
  have hrw : big / lam * lam = big := div_mul_cancel₀ big (ne_of_gt hlam)
  rw [hrw]
  exact ⟨hlam, hlb, hall⟩

end UCPlanar.Support
