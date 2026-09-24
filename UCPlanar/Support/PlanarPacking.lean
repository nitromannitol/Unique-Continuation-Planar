/- Finite separated subsets and bounded-neighborhood counting. -/
import UCPlanar.Support.Density
import Mathlib.Data.Finset.Max

open scoped Classical

/-- A finite set has a separated subset whose relation neighborhoods cover it. -/
theorem UCPlanar.Support.exists_separated_cover {V : Type*} [DecidableEq V]
    (S : Finset V) (R : V → V → Prop) (hsymm : ∀ ⦃x y⦄, R x y → R y x) :
    ∃ T ⊆ S, (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ R x y) ∧
      ∀ x ∈ S, ∃ y ∈ T, x = y ∨ R x y := by
  classical
  let sep : Finset V → Prop := fun T => ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ R x y
  let A := S.powerset.filter sep
  have hA : A.Nonempty := ⟨∅, by simp [A, sep]⟩
  obtain ⟨T, hT, hmax⟩ := A.exists_max_image Finset.card hA
  have hT' : T ∈ S.powerset ∧ sep T := by simpa only [A, Finset.mem_filter] using hT
  obtain ⟨hTS, hsep⟩ := hT'
  refine ⟨T, Finset.mem_powerset.mp hTS, hsep, ?_⟩
  intro x hx
  by_contra hn
  push Not at hn
  have hxT : x ∉ T := fun h => (hn x h).1 rfl
  have hi : insert x T ∈ A := by
    change insert x T ∈ S.powerset.filter sep
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset hx (Finset.mem_powerset.mp hTS)), ?_⟩
    intro u hu v hv huv
    rcases Finset.mem_insert.mp hu with rfl | huT
    · rcases Finset.mem_insert.mp hv with rfl | hvT
      · exact False.elim (huv rfl)
      · exact (hn v hvT).2
    · rcases Finset.mem_insert.mp hv with rfl | hvT
      · exact fun h => (hn u huT).2 (hsymm h)
      · exact hsep u huT v hvT huv
  have hcard := hmax (insert x T) hi
  rw [Finset.card_insert_of_notMem hxT] at hcard
  omega

/-- A cover by bounded finite neighborhoods controls cardinality. -/
theorem UCPlanar.Support.card_le_of_cover {V : Type*} [DecidableEq V]
    (S T : Finset V) (B : V → Finset V) (K : ℕ)
    (hcover : ∀ x ∈ S, ∃ y ∈ T, x ∈ B y)
    (hbound : ∀ y ∈ T, (B y).card ≤ K) : S.card ≤ T.card * K := by
  have hsub : S ⊆ T.biUnion B := by
    intro x hx
    exact Finset.mem_biUnion.mpr (hcover x hx)
  exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le_card_mul T B K hbound)

/-- Uniform relation-neighborhood bounds give a quantitatively large separated subset. -/
theorem UCPlanar.Support.exists_separated_card {V : Type*} [DecidableEq V]
    (S : Finset V) (R : V → V → Prop) (hsymm : ∀ ⦃x y⦄, R x y → R y x)
    (K : ℕ) (hbound : ∀ y ∈ S, (S.filter (fun x => x = y ∨ R x y)).card ≤ K) :
    ∃ T ⊆ S, (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ R x y) ∧ S.card ≤ T.card * K := by
  classical
  obtain ⟨T, hTS, hsep, hcover⟩ := UCPlanar.Support.exists_separated_cover S R hsymm
  refine ⟨T, hTS, hsep, UCPlanar.Support.card_le_of_cover S T
    (fun y => S.filter (fun x => x = y ∨ R x y)) K ?_ ?_⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover x hx
    exact ⟨y, hy, Finset.mem_filter.mpr ⟨hx, hxy⟩⟩
  · exact fun y hy => hbound y (hTS hy)

/-- Packing and a two-to-one boundary charge give a coefficient strictly below one. -/
theorem UCPlanar.Support.density_bound_of_packing {V : Type*} [DecidableEq V]
    (S Z T : Finset V) (hZS : Z ⊆ S) (K : ℕ) (hK : 0 < K)
    (hpack : Z.card ≤ T.card * K) (hcharge : T.card ≤ 2 * (S \ Z).card) :
    0 < 2 * (K : ℝ) / (2 * K + 1) ∧ 2 * (K : ℝ) / (2 * K + 1) < 1 ∧
      (Z.card : ℝ) ≤ (2 * (K : ℝ) / (2 * K + 1)) * S.card := by
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  have hd : 0 < 2 * (K : ℝ) + 1 := by positivity
  refine ⟨div_pos (by positivity) hd, (div_lt_one hd).mpr (by linarith), ?_⟩
  have hp : (Z.card : ℝ) ≤ (T.card : ℝ) * K := by exact_mod_cast hpack
  have ht : (T.card : ℝ) ≤ 2 * ((S \ Z).card : ℝ) := by exact_mod_cast hcharge
  have hz : (Z.card : ℝ) ≤ 2 * (K : ℝ) * (S \ Z).card := by
    nlinarith [mul_le_mul_of_nonneg_right ht hk.le]
  have hsum : (Z.card : ℝ) + (S \ Z).card = S.card := by
    exact_mod_cast (by simpa only [Nat.add_comm] using Finset.card_sdiff_add_card_eq_card hZS)
  simpa only [hsum] using UCPlanar.Support.packing_ratio (Z.card : ℝ) (S \ Z).card K hk hz

/-- If each unselected index follows a selected one, at least half the indices are selected. -/
theorem UCPlanar.Support.card_le_two_mul_of_predecessor (n : ℕ) (A : Finset ℕ)
    (h : ∀ j < n, j ∉ A → 0 < j ∧ j - 1 ∈ A) : n ≤ 2 * A.card := by
  have hb : (Finset.range n \ A).card ≤ A.card := by
    apply Finset.card_le_card_of_injOn (fun j => j - 1)
    · intro j hj
      obtain ⟨hjn, hja⟩ := Finset.mem_sdiff.mp hj
      exact (h j (Finset.mem_range.mp hjn) hja).2
    · intro j hj k hk he
      obtain ⟨hjn, hja⟩ := Finset.mem_sdiff.mp hj
      obtain ⟨hkn, hka⟩ := Finset.mem_sdiff.mp hk
      have hjpos := (h j (Finset.mem_range.mp hjn) hja).1
      have hkpos := (h k (Finset.mem_range.mp hkn) hka).1
      change j - 1 = k - 1 at he
      omega
  have hc := Finset.card_le_card_sdiff_add_card (s := Finset.range n) (t := A)
  rw [Finset.card_range] at hc
  omega

