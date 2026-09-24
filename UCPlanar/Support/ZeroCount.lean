/- Pigeonhole with bounded multiplicity, for the boundary radius of the zero case. -/
import Mathlib

open scoped BigOperators Classical

namespace UCPlanar.Support

/-- **Pigeonhole with bounded multiplicity.** If each of `M` subsets of a finite set `S` is
covered with multiplicity at most `K`, one of them holds at most `K |S| / M` elements. This is
the counting behind Step 2 of Section 3, where the subsets are the vertices near the successive
boundary radii. -/
theorem exists_sparse_index {V : Type*} (S : Finset V) (T : ℕ → Finset V)
    (M K : ℕ) (hM : 0 < M)
    (hsub : ∀ m, m < M → T m ⊆ S)
    (hmult : ∀ x ∈ S, ((Finset.range M).filter (fun m => x ∈ T m)).card ≤ K) :
    ∃ m < M, ((T m).card : ℝ) ≤ (K : ℝ) * S.card / M := by
  classical
  have hfil : ∀ m, m < M → S.filter (fun x => x ∈ T m) = T m := by
    intro m hm
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub m hm h, h⟩⟩
  have hcount : ∑ m ∈ Finset.range M, (T m).card ≤ K * S.card := by
    have h1 : ∑ m ∈ Finset.range M, (T m).card
        = ∑ m ∈ Finset.range M, ∑ x ∈ S, (if x ∈ T m then 1 else 0) := by
      refine Finset.sum_congr rfl ?_
      intro m hm
      rw [← Finset.card_filter, hfil m (Finset.mem_range.mp hm)]
    have h2 : ∑ m ∈ Finset.range M, ∑ x ∈ S, (if x ∈ T m then 1 else 0)
        = ∑ x ∈ S, ∑ m ∈ Finset.range M, (if x ∈ T m then 1 else 0) := Finset.sum_comm
    have h3 : ∀ x ∈ S, ∑ m ∈ Finset.range M, (if x ∈ T m then 1 else 0) ≤ K := by
      intro x hx
      rw [← Finset.card_filter]
      exact hmult x hx
    calc ∑ m ∈ Finset.range M, (T m).card
        = ∑ x ∈ S, ∑ m ∈ Finset.range M, (if x ∈ T m then 1 else 0) := by rw [h1, h2]
      _ ≤ ∑ _x ∈ S, K := Finset.sum_le_sum h3
      _ = K * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hM' : (0 : ℝ) < M := by positivity
  have hsum' : ∑ m ∈ Finset.range M, ((T m).card : ℝ)
      ≤ ∑ _m ∈ Finset.range M, ((K : ℝ) * S.card / M) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel₀ _ (ne_of_gt hM')]
    exact_mod_cast hcount
  obtain ⟨m, hm, hle⟩ := Finset.exists_le_of_sum_le
    (Finset.nonempty_range_iff.mpr (by omega)) hsum'
  exact ⟨m, Finset.mem_range.mp hm, hle⟩

/-- **A connected set carrying a walk is at least as large as the distance between its ends.** -/
theorem card_ge_of_walk {V : Type*} {G : SimpleGraph V} {x w : V} (C : Finset V)
    (p : G.Walk x w) (hsub : ∀ z ∈ p.support, z ∈ C) : G.dist x w + 1 ≤ C.card := by
  classical
  have hbp : p.bypass.IsPath := SimpleGraph.Walk.bypass_isPath p
  have hsup : p.bypass.support ⊆ p.support := SimpleGraph.Walk.support_bypass_subset_support p
  have hcard : p.bypass.support.toFinset.card = p.bypass.length + 1 := by
    rw [List.toFinset_card_of_nodup hbp.support_nodup, SimpleGraph.Walk.length_support]
  have hsub' : p.bypass.support.toFinset ⊆ C := by
    intro z hz
    exact hsub z (hsup (List.mem_toFinset.mp hz))
  have hle : p.bypass.support.toFinset.card ≤ C.card := Finset.card_le_card hsub'
  have hdist : G.dist x w ≤ p.bypass.length := SimpleGraph.dist_le p.bypass
  omega

end UCPlanar.Support
