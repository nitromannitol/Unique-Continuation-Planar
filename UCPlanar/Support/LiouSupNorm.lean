/-
The sup norm over a ball controls the value at a point.
-/
import UCPlanar.Support.Periodic

open scoped Classical

-- FROZEN-STATEMENT-BEGIN
/-- A point of a finite set is bounded by the sup norm over it. -/
theorem UCPlanar.Support.abs_le_supNorm {V : Type*} (S : Finset V) (f : V → ℝ) {x : V}
    (hx : x ∈ S) : |f x| ≤ UCPlanar.supNorm S f
-- FROZEN-STATEMENT-END
:= by
  simpa [UCPlanar.supNorm, Real.norm_eq_abs] using
    NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun x => ‖f x‖₊) hx)
