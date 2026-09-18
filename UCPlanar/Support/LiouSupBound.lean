/-
A pointwise bound on a finite set bounds its supremum norm.
-/
import UCPlanar.Support.Periodic

open scoped Classical

namespace UCPlanar.Support

/-- If every element of a finite set satisfies `|f x| ≤ M`, then the supremum norm of
`f` over that set is at most `M`. -/
theorem supNorm_le_of_forall_le {V : Type*} (S : Finset V) (f : V → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (h : ∀ x ∈ S, |f x| ≤ M) : UCPlanar.supNorm S f ≤ M := by
  rw [UCPlanar.supNorm]
  have hsup : S.sup (fun x => ‖f x‖₊) ≤ ⟨M, hM⟩ := by
    apply Finset.sup_le_iff.mpr
    intro x hx
    rw [← NNReal.coe_le_coe]
    show ‖f x‖ ≤ M
    rw [Real.norm_eq_abs]
    exact h x hx
  exact_mod_cast hsup

end UCPlanar.Support
