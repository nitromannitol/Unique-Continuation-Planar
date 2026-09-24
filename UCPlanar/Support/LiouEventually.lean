/-
The density limit gives an eventual lower bound on the bounded density.
-/
import UCPlanar.Support.Growth

open scoped Classical

namespace UCPlanar.Support

/-- The density limit gives an eventual lower bound on the bounded density. -/
theorem eventually_density_ge {V : Type*} (P : UCPlanar.PeriodicGraph V) (o : V)
    (f : V → ℝ) (ε δ : ℝ) (hδ : 0 < δ) (h : P.HasBoundedDensity o f ε) :
    ∀ᶠ n : ℕ in Filter.atTop, 1 - ε - δ ≤ UCPlanar.boundedDensity (P.ball o n) f 1 := by
  obtain ⟨d, hd, hlim⟩ := h
  have hmem : d ∈ Set.Ioi (1 - ε - δ) := by
    simp only [Set.mem_Ioi]
    linarith
  filter_upwards [hlim.eventually (isOpen_Ioi.mem_nhds hmem)] with n hn
  exact le_of_lt hn

end UCPlanar.Support
