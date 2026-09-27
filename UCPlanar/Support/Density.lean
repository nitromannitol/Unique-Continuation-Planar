/-
Finite exceptional sets and the coefficient obtained from a separated subset of zeros.
-/
import LatticeProb.Network.Basic
import Mathlib.Tactic

open scoped BigOperators Classical
set_option autoImplicit false

/-- **A packing-ratio bound.**  If `z ≤ 2kb` for `k > 0`, then `z` is at most the fraction
`2k/(2k+1)` of the total `z+b`, by clearing denominators and `nlinarith`. -/
theorem UCPlanar.Support.packing_ratio (z b k : ℝ) (hk : 0 < k) (h : z ≤ 2*k*b) :
    z ≤ (2*k/(2*k+1))*(z+b) := by
  have hd : 0 < 2 * k + 1 := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hd]
  nlinarith

/-- **Fewer than one bad index means none.**  If the (real-cast) count of indices in `s` with
`|f x| > 1` is less than `1`, that count is in fact `0`, so `|f x| ≤ 1` holds for every `x ∈ s`. -/
theorem UCPlanar.Support.small_bad_count {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h : ((s.filter (fun x => 1 < |f x|)).card : ℝ) < 1) : ∀ x ∈ s, |f x| ≤ 1 := by
  classical
  have hz : (s.filter (fun x => 1 < |f x|)).card = 0 := Nat.cast_lt_one.mp h
  have he := Finset.card_eq_zero.mp hz
  intro x hx
  by_contra hf
  have hx' : x ∈ s.filter (fun x => 1 < |f x|) := Finset.mem_filter.mpr ⟨hx, lt_of_not_ge hf⟩
  rw [he] at hx'
  exact Finset.notMem_empty x hx'
