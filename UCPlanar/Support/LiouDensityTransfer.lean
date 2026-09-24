/-
The bounded density over a subset is at least the density over a containing set,
up to the ratio of the two cardinalities.
-/
import UCPlanar.Support.LiouTransfer
import UCPlanar.Basic

open scoped Classical

namespace UCPlanar.Support

/-- Cardinality form: the density of a predicate over a nonempty subset is at least
the density over a containing set, up to the ratio of the two cardinalities. -/
theorem card_density_subset_ge {α : Type*} (A B : Finset α) (p : α → Prop) [DecidablePred p]
    (hsub : A ⊆ B) (hpos : 0 < A.card) :
    ((A.filter p).card : ℝ) / A.card ≥
      ((B.filter p).card : ℝ) / B.card - ((B.card - A.card : ℕ) : ℝ) / A.card := by
  have hAcard : (0:ℝ) < A.card := by exact_mod_cast hpos
  have hcard : A.card ≤ B.card := Finset.card_le_card hsub
  have hBcard : (0:ℝ) < B.card := by exact_mod_cast lt_of_lt_of_le hpos hcard
  have hfilt : (A.filter p).card ≤ (B.filter p).card :=
    Finset.card_le_card (Finset.filter_subset_filter p hsub)
  have hkey : (B.filter p).card ≤ (A.filter p).card + (B.card - A.card) := by
    have h1 : (B.filter p).card ≤ (A.filter p).card + (B \ A).card := by
      calc (B.filter p).card ≤ ((A.filter p) ∪ (B \ A)).card := by
            apply Finset.card_le_card
            intro x hx
            rw [Finset.mem_filter] at hx
            rw [Finset.mem_union]
            by_cases hxA : x ∈ A
            · exact Or.inl (Finset.mem_filter.mpr ⟨hxA, hx.2⟩)
            · exact Or.inr (Finset.mem_sdiff.mpr ⟨hx.1, hxA⟩)
        _ ≤ (A.filter p).card + (B \ A).card := Finset.card_union_le _ _
    have h2 : (B \ A).card = B.card - A.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
    omega
  have hkeyR : ((B.filter p).card : ℝ) ≤ ((A.filter p).card : ℝ) + ((B.card - A.card : ℕ) : ℝ) := by
    exact_mod_cast hkey
  have hfiltR : ((A.filter p).card : ℝ) ≤ ((B.filter p).card : ℝ) := by exact_mod_cast hfilt
  have hcardR : (A.card : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hcard
  rw [ge_iff_le, sub_le_iff_le_add]
  field_simp
  nlinarith [hkeyR, hfiltR, hcardR, hAcard, hBcard]

/-- The bounded density over a nonempty subset is at least the bounded density over a
containing set, up to the ratio of the two cardinalities. -/
theorem boundedDensity_square_ge {V : Type*} (P : UCPlanar.PeriodicGraph V) (o : V)
    (f : V → ℝ) (R : ℝ) (n : ℕ) (hsub : (P.square R : Set V) ⊆ (P.ball o n : Set V))
    (hpos : 0 < (P.square R).card) :
    UCPlanar.boundedDensity (P.square R) f 1 ≥
      UCPlanar.boundedDensity (P.ball o n) f 1 -
        ((P.ball o n).card - (P.square R).card : ℝ) / (P.square R).card := by
  have hsub' : P.square R ⊆ P.ball o n := by
    intro x hx
    exact hsub (by simpa using hx)
  have h := card_density_subset_ge (P.square R) (P.ball o n) (fun x => |f x| ≤ 1) hsub' hpos
  have hcast : (((P.ball o n).card - (P.square R).card : ℕ) : ℝ) =
      ((P.ball o n).card : ℝ) - ((P.square R).card : ℝ) := by
    rw [Nat.cast_sub (Finset.card_le_card hsub')]
  simpa [UCPlanar.boundedDensity, hcast] using h

end UCPlanar.Support
