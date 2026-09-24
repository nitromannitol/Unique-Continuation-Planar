/-
Iteration of a geometric recursion, the arithmetic core of the nested-domain
bound on mixed differences.
-/
import Mathlib

open scoped BigOperators Classical
set_option autoImplicit false

namespace UCPlanar.Support

theorem geom_iterate_le (a : ℕ → ℝ) (C R B : ℝ) (m : ℕ)
    (hC : 0 ≤ C) (hR : 0 < R) (ha : ∀ k, 0 ≤ a k)
    (hstep : ∀ k, k < m → a k ≤ (C / R) * a (k + 1)) (htop : a m ≤ B) :
    a 0 ≤ (C / R) ^ m * B := by
  induction m generalizing a with
  | zero => simpa using htop
  | succ m ih =>
    have h0 := hstep 0 (Nat.succ_pos m)
    have h1 : a 1 ≤ (C / R) ^ m * B :=
      ih (fun k => a (k + 1)) (fun k => ha (k + 1))
        (fun k hk => hstep (k + 1) (by omega)) htop
    calc a 0 ≤ (C / R) * a 1 := h0
      _ ≤ (C / R) * ((C / R) ^ m * B) :=
          mul_le_mul_of_nonneg_left h1 (div_nonneg hC (le_of_lt hR))
      _ = (C / R) ^ (m + 1) * B := by rw [pow_succ]; ring

theorem derivBound_iterate (a : ℕ → ℝ) (C R B : ℝ) (m : ℕ)
    (hC : 0 ≤ C) (hR : 0 < R) (ha : ∀ k, 0 ≤ a k)
    (hstep : ∀ k, k < m + 1 → a k ≤ (C / R) * a (k + 1))
    (htop : a (m + 1) ≤ B) :
    a 0 ≤ (C / R) ^ (m + 1) * B := by
  exact UCPlanar.Support.geom_iterate_le a C R B (m + 1) hC hR ha hstep htop

end UCPlanar.Support
