/- Counting component labels in an ordered list of boundary contacts. -/
import UCPlanar.Support.PlanarPacking
import Mathlib.Tactic

open scoped Classical

/-- A set of indices whose distinct elements are consecutive has at most two elements. -/
theorem UCPlanar.Support.card_le_two_of_close_indices (S : Finset ℕ)
    (h : ∀ i ∈ S, ∀ j ∈ S, i < j → j ≤ i + 1) : S.card ≤ 2 := by
  obtain he | hn := S.eq_empty_or_nonempty
  · simp [he]
  obtain ⟨k, hk, hmin⟩ := S.exists_min_image id hn
  have hs : S ⊆ {k, k + 1} := by
    intro j hj
    have hkj : k ≤ j := hmin j hj
    have hjk : j ≤ k + 1 := by
      by_cases he : k = j
      · omega
      · exact h k hk j hj (by omega)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  exact (Finset.card_le_card hs).trans Finset.card_le_two

/-- Every label has a first occurrence up to the given index. -/
theorem UCPlanar.Support.exists_first_label {A : Type*} (p : ℕ → A) (j : ℕ) :
    ∃ k ≤ j, p k = p j ∧ ∀ i < k, p i ≠ p j := by
  classical
  have hex : ∃ k, p k = p j := ⟨j, rfl⟩
  exact ⟨Nat.find hex, Nat.find_min' hex rfl, Nat.find_spec hex,
    fun i hi => Nat.find_min hex hi⟩

/-- Labels that cannot recur at nonconsecutive indices count each index at most twice. -/
theorem UCPlanar.Support.card_le_two_mul_labels {A : Type*} [DecidableEq A]
    (S : Finset ℕ) (T : Finset A) (f : ℕ → A)
    (hmap : ∀ i ∈ S, f i ∈ T)
    (hfar : ∀ i ∈ S, ∀ j ∈ S, i + 1 < j → f i ≠ f j) :
    S.card ≤ 2 * T.card := by
  apply Finset.card_le_mul_card_image_of_maps_to hmap 2
  intro a _
  apply UCPlanar.Support.card_le_two_of_close_indices
  intro i hi j hj _
  obtain ⟨hiS, hi⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjS, hj⟩ := Finset.mem_filter.mp hj
  by_contra hn
  exact hfar i hiS j hjS (by omega) (hi.trans hj.symm)

/-- The first occurrence of the label at index `j`. -/
noncomputable def UCPlanar.Support.firstLabelIndex {A : Type*} (p : ℕ → A) (j : ℕ) : ℕ :=
  (UCPlanar.Support.exists_first_label p j).choose

/-- The first occurrence is bounded by the current index and is minimal. -/
theorem UCPlanar.Support.firstLabelIndex_spec {A : Type*} (p : ℕ → A) (j : ℕ) :
    UCPlanar.Support.firstLabelIndex p j ≤ j ∧
    p (UCPlanar.Support.firstLabelIndex p j) = p j ∧
    ∀ i < UCPlanar.Support.firstLabelIndex p j, p i ≠ p j := by
  exact (UCPlanar.Support.exists_first_label p j).choose_spec

/-- Equal labels have the same first occurrence. -/
theorem UCPlanar.Support.firstLabelIndex_eq_of_label_eq {A : Type*}
    (p : ℕ → A) {i j : ℕ} (he : p i = p j) :
    UCPlanar.Support.firstLabelIndex p i = UCPlanar.Support.firstLabelIndex p j := by
  have hi := UCPlanar.Support.firstLabelIndex_spec p i
  have hj := UCPlanar.Support.firstLabelIndex_spec p j
  rcases lt_trichotomy (UCPlanar.Support.firstLabelIndex p i)
      (UCPlanar.Support.firstLabelIndex p j) with h | h | h
  · exact False.elim (hj.2.2 _ h (hi.2.1.trans he))
  · exact h
  · exact False.elim (hi.2.2 _ h (hj.2.1.trans he.symm))

/-- Charge the first two positions of a plus label to it, and later positions to a minus label. -/
noncomputable def UCPlanar.Support.scanLabel {A B : Type*}
    (p : ℕ → A) (m : ℕ → B) (j : ℕ) : Sum A B :=
  if j ≤ UCPlanar.Support.firstLabelIndex p j + 1 then Sum.inl (p j)
  else Sum.inr (m (j - 1))

/-- Every charge belongs to one of the two finite label sets. -/
theorem UCPlanar.Support.scanLabel_mem {A B : Type*} [DecidableEq A] [DecidableEq B]
    (p : ℕ → A) (m : ℕ → B) (P : Finset A) (M : Finset B) (n : ℕ)
    (hp : ∀ i < n, p i ∈ P) (hm : ∀ i < n, m i ∈ M) {j : ℕ} (hj : j < n) :
    UCPlanar.Support.scanLabel p m j ∈ P.disjSum M := by
  unfold UCPlanar.Support.scanLabel
  split
  · exact Finset.inl_mem_disjSum.mpr (hp j hj)
  · exact Finset.inr_mem_disjSum.mpr (hm (j - 1) (by omega))

/-- Alternating component connections forbid equal charges at nonconsecutive indices. -/
theorem UCPlanar.Support.scanLabel_ne_of_far {A B : Type*}
    (p : ℕ → A) (m : ℕ → B) (n : ℕ)
    (hcross : ∀ k a b c : ℕ, k < a → a < b → b < c → c < n →
      p k = p b → m a ≠ m c)
    {i j : ℕ} (_hi : i < n) (hj : j < n) (hij : i + 1 < j) :
    UCPlanar.Support.scanLabel p m i ≠ UCPlanar.Support.scanLabel p m j := by
  intro he
  unfold UCPlanar.Support.scanLabel at he
  split_ifs at he with hi' hj' hj'
  · have hp : p i = p j := Sum.inl.inj he
    have hk := UCPlanar.Support.firstLabelIndex_eq_of_label_eq p hp
    have hs := UCPlanar.Support.firstLabelIndex_spec p i
    omega
  · have hm : m (i - 1) = m (j - 1) := Sum.inr.inj he
    have hs := UCPlanar.Support.firstLabelIndex_spec p i
    exact hcross (UCPlanar.Support.firstLabelIndex p i) (i - 1) i (j - 1)
      (by omega) (by omega) (by omega) (by omega) hs.2.1 hm

/-- Two nonalternating families of labels account for at least half the contacts. -/
theorem UCPlanar.Support.count_labels_of_nonalternating {A B : Type*}
    [DecidableEq A] [DecidableEq B]
    (p : ℕ → A) (m : ℕ → B) (P : Finset A) (M : Finset B) (n : ℕ)
    (hp : ∀ i < n, p i ∈ P) (hm : ∀ i < n, m i ∈ M)
    (hcross : ∀ k a b c : ℕ, k < a → a < b → b < c → c < n →
      p k = p b → m a ≠ m c) : n ≤ 2 * (P.card + M.card) := by
  have h := UCPlanar.Support.card_le_two_mul_labels (Finset.range n) (P.disjSum M)
    (UCPlanar.Support.scanLabel p m)
    (fun i hi => UCPlanar.Support.scanLabel_mem p m P M n hp hm (Finset.mem_range.mp hi))
    (fun i hi j hj hij => UCPlanar.Support.scanLabel_ne_of_far p m n hcross
      (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij)
  simpa only [Finset.card_range, Finset.card_disjSum] using h

/-- Disjoint sign labels on the boundary give the two-to-one boundary charge. -/
theorem UCPlanar.Support.boundary_count_of_nonalternating {V : Type*} [DecidableEq V]
    (p m : ℕ → V) (P M B : Finset V) (n : ℕ)
    (hP : P ⊆ B) (hM : M ⊆ B) (hPM : Disjoint P M)
    (hp : ∀ i < n, p i ∈ P) (hm : ∀ i < n, m i ∈ M)
    (hcross : ∀ k a b c : ℕ, k < a → a < b → b < c → c < n →
      p k = p b → m a ≠ m c) : n ≤ 2 * B.card := by
  have hc := Finset.card_le_card (Finset.union_subset hP hM)
  rw [Finset.card_union_of_disjoint hPM] at hc
  exact (UCPlanar.Support.count_labels_of_nonalternating p m P M n hp hm hcross).trans
    (Nat.mul_le_mul_left 2 hc)
