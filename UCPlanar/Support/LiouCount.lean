/-
The exceptional count and the bounded density are complementary.
-/
import UCPlanar.Basic

open scoped Classical

/-- A density bound on a nonempty finite set bounds the exceptional count. -/
theorem UCPlanar.Support.exceptionalCount_le_of_density {V : Type*} (S : Finset V)
    (f : V → ℝ) (ε : ℝ) (hcard : 0 < S.card)
    (h : 1 - ε ≤ UCPlanar.boundedDensity S f 1) :
    (UCPlanar.exceptionalCount S f 1 : ℝ) ≤ ε * S.card
:= by
  simp only [UCPlanar.boundedDensity] at h
  simp only [UCPlanar.exceptionalCount]
  have hpart : (S.filter (fun x => |f x| ≤ 1)).card + (S.filter (fun x => 1 < |f x|)).card = S.card := by
    simp only [not_le.symm, Finset.card_filter_add_card_filter_not]
  have hpos : (0 : ℝ) < S.card := by exact_mod_cast hcard
  rw [le_div_iff₀ hpos] at h
  have hexpand : (1 - ε) * (S.card : ℝ) = (S.card : ℝ) - ε * (S.card : ℝ) := by ring
  rw [hexpand] at h
  have hpartR : ((S.filter (fun x => |f x| ≤ 1)).card : ℝ) +
      ((S.filter (fun x => 1 < |f x|)).card : ℝ) = (S.card : ℝ) := by exact_mod_cast hpart
  have hE : ((S.filter (fun x => 1 < |f x|)).card : ℝ) =
      (S.card : ℝ) - ((S.filter (fun x => |f x| ≤ 1)).card : ℝ) := by linarith
  rw [hE]
  linarith
