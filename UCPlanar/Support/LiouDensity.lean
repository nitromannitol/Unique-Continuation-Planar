/-
The density hypothesis gives an eventual lower bound on the bounded density.
-/
import UCPlanar.Support.Growth

open scoped Classical

/-- A bounded-value density limit above `1 - ε` is eventually above `1 - ε - δ`. -/
theorem UCPlanar.Support.eventually_density_of_hasBoundedDensity {V : Type*}
    (P : UCPlanar.PeriodicGraph V) (o : V) (f : V → ℝ) (ε δ : ℝ)
    (h : P.HasBoundedDensity o f ε) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      1 - ε - δ ≤ UCPlanar.boundedDensity (P.ball o n) f 1
:= by
  obtain ⟨d, hd, hlim⟩ := h
  have hlt : 1 - ε - δ < d := by linarith
  exact (hlim.eventually (isOpen_Ioi.mem_nhds hlt)).mono fun n hn => le_of_lt hn
