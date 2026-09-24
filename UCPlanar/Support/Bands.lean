/- Geometric bands of values: one band is sparse. -/
import UCPlanar.Basic
import Mathlib.Tactic

open scoped BigOperators Classical

namespace UCPlanar.Support

/-- **Pigeonhole over geometric bands.** Among `M` disjoint geometric bands of values, one
contains at most the average number of vertices of a finite set. -/
theorem exists_sparse_band {V : Type*} (S : Finset V) (f : V → ℝ) (ρ : ℝ) (hρ : 1 < ρ)
    (M : ℕ) (hM : 0 < M) :
    ∃ m < M, ((S.filter (fun x => ρ ^ m ≤ |f x| ∧ |f x| < ρ ^ (m + 1))).card : ℝ)
      ≤ (S.card : ℝ) / M := by
  classical
  set T : ℕ → Finset V := fun m => S.filter (fun x => ρ ^ m ≤ |f x| ∧ |f x| < ρ ^ (m + 1))
    with hT
  have hdisj : ∀ m ∈ Finset.range M, ∀ m' ∈ Finset.range M, m ≠ m' →
      Disjoint (T m) (T m') := by
    intro m _ m' _ hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [hT, Finset.mem_filter] at hx hx'
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 : ρ ^ (m + 1) ≤ ρ ^ m' := pow_le_pow_right₀ hρ.le (by omega)
      linarith [hx.2.2, hx'.2.1]
    · have h1 : ρ ^ (m' + 1) ≤ ρ ^ m := pow_le_pow_right₀ hρ.le (by omega)
      linarith [hx'.2.2, hx.2.1]
  have hsum : ∑ m ∈ Finset.range M, (T m).card ≤ S.card := by
    rw [← Finset.card_biUnion hdisj]
    refine Finset.card_le_card ?_
    intro x hx
    simp only [Finset.mem_biUnion] at hx
    obtain ⟨m, _, hxm⟩ := hx
    exact (Finset.mem_filter.mp hxm).1
  have hsum' : ∑ m ∈ Finset.range M, ((T m).card : ℝ)
      ≤ ∑ _m ∈ Finset.range M, (S.card : ℝ) / M := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hM' : (0 : ℝ) < M := by positivity
    rw [mul_div_cancel₀ _ (ne_of_gt hM')]
    exact_mod_cast hsum
  obtain ⟨m, hm, hle⟩ := Finset.exists_le_of_sum_le
    (Finset.nonempty_range_iff.mpr (by omega)) hsum'
  exact ⟨m, Finset.mem_range.mp hm, hle⟩

/-- **The pigeonhole threshold of the paper's Step 1.** For every tolerance there is a
threshold `A` between `1` and `ρ ^ M` whose band `[A, ρ A)` holds fewer than that many
vertices. -/
theorem exists_sparse_threshold {V : Type*} (S : Finset V) (f : V → ℝ) (ρ : ℝ) (hρ : 1 < ρ)
    (δ : ℝ) (M : ℕ) (hM : 0 < M) (hsmall : (S.card : ℝ) < δ * M) :
    ∃ A : ℝ, 1 ≤ A ∧ A ≤ ρ ^ M ∧
      ((S.filter (fun x => A ≤ |f x| ∧ |f x| < ρ * A)).card : ℝ) < δ := by
  classical
  obtain ⟨m, hm, hle⟩ := exists_sparse_band S f ρ hρ M hM
  have hM' : (0 : ℝ) < M := by positivity
  refine ⟨ρ ^ m, one_le_pow₀ hρ.le, pow_le_pow_right₀ hρ.le (le_of_lt hm), ?_⟩
  have hband : S.filter (fun x => ρ ^ m ≤ |f x| ∧ |f x| < ρ * ρ ^ m)
      = S.filter (fun x => ρ ^ m ≤ |f x| ∧ |f x| < ρ ^ (m + 1)) := by
    refine Finset.filter_congr ?_
    intro x _
    rw [pow_succ, mul_comm]
  rw [hband]
  calc ((S.filter (fun x => ρ ^ m ≤ |f x| ∧ |f x| < ρ ^ (m + 1))).card : ℝ)
      ≤ (S.card : ℝ) / M := hle
    _ < δ := by rw [div_lt_iff₀ hM']; linarith

end UCPlanar.Support
