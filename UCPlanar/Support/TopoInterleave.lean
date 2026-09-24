/- Interleaved drawn walks in a drawn cycle share a vertex. -/
import UCPlanar.Support.TopoCross

open Set SimpleGraph

open scoped Classical

namespace UCPlanar.Support

/-- Reversing a walk does not move its drawing. -/
theorem walkTrace_reverse {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {x y : V} (w : G.Walk x y) :
    E.walkTrace w.reverse = E.walkTrace w := by
  refine subset_antisymm ?_ ?_
  · refine walkTrace_mono_of_edges E w.reverse w (fun e he => ?_) w.end_mem_support
    rw [SimpleGraph.Walk.edges_reverse] at he
    exact List.mem_reverse.mp he
  · refine walkTrace_mono_of_edges E w w.reverse (fun e he => ?_) w.reverse.end_mem_support
    rw [SimpleGraph.Walk.edges_reverse]
    exact List.mem_reverse.mpr he

/-- Splitting a walk at one of its vertices. -/
theorem exists_split {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {x y v : V} (w : G.Walk x y) (hv : v ∈ w.support) :
    ∃ (w₁ : G.Walk x v) (w₂ : G.Walk v y),
      w₁.length + w₂.length = w.length ∧
      (∀ z ∈ w₁.support, z ∈ w.support) ∧ (∀ z ∈ w₂.support, z ∈ w.support) ∧
      E.walkTrace w₁ ⊆ E.walkTrace w ∧ E.walkTrace w₂ ⊆ E.walkTrace w := by
  refine ⟨w.takeUntil v hv, w.dropUntil v hv, ?_, ?_, ?_, ?_, ?_⟩
  · conv_rhs => rw [← w.take_spec hv]
    rw [SimpleGraph.Walk.length_append]
  · exact fun z hz => w.support_takeUntil_subset_support hv hz
  · exact fun z hz => w.support_dropUntil_subset_support hv hz
  · conv_rhs => rw [← w.take_spec hv]
    rw [E.walkTrace_append]
    exact Set.subset_union_left
  · conv_rhs => rw [← w.take_spec hv]
    rw [E.walkTrace_append]
    exact Set.subset_union_right

/-- **Two drawn walks whose ends interleave around a drawn cycle, both drawn in the closed
cycle domain, share a vertex.** -/
theorem exists_common_vertex_of_interleaved {V : Type*} {G : SimpleGraph V} {o : V}
    (E : UCPlanar.PlaneEmbedding G) (γ : G.Walk o o) (hγ : γ.IsCycle) :
    ∀ (n : ℕ) (i j k l : ℕ), i < j → j < k → k < l → l < γ.length →
    ∀ (p : G.Walk (γ.getVert i) (γ.getVert k)) (q : G.Walk (γ.getVert j) (γ.getVert l)),
      p.length + q.length ≤ n →
      E.walkTrace p ⊆ E.closedCycleDomain γ → E.walkTrace q ⊆ E.closedCycleDomain γ →
      ∃ v ∈ p.support, v ∈ q.support := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro i j k l hij hjk hkl hl p q hn hpd hqd
    by_cases hcp : IsChord γ p
    · by_cases hcq : IsChord γ q
      · exact exists_common_vertex_of_chords E γ hγ hij hjk hkl hl p q hpd hqd hcp hcq
      · -- the second walk returns to the cycle: split it there
        rw [IsChord] at hcq
        push Not at hcq
        obtain ⟨w, hwq, hwγ, hwj, hwl⟩ := hcq
        by_cases hwp : w ∈ p.support
        · exact ⟨w, hwp, hwq⟩
        obtain ⟨r, hr, hrle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hwγ
        obtain ⟨r', hrv, hrlt⟩ : ∃ r' : ℕ, γ.getVert r' = w ∧ r' < γ.length := by
          by_cases hrz : r = γ.length
          · refine ⟨0, ?_, by omega⟩
            rw [SimpleGraph.Walk.getVert_zero, ← SimpleGraph.Walk.getVert_length γ, ← hrz]
            exact hr
          · exact ⟨r, hr, by omega⟩
        have hri : r' ≠ i := by
          intro h
          exact hwp (by rw [← hrv, h]; exact p.start_mem_support)
        have hrk : r' ≠ k := by
          intro h
          exact hwp (by rw [← hrv, h]; exact p.end_mem_support)
        obtain ⟨q₁, q₂, hlen, hs₁, hs₂, ht₁, ht₂⟩ :=
          exists_split E q (show γ.getVert r' ∈ q.support by rw [hrv]; exact hwq)
        have hq₁len : q₁.length ≠ 0 := by
          intro h0
          exact hwj (by rw [← hrv, ← SimpleGraph.Walk.eq_of_length_eq_zero h0])
        have hq₂len : q₂.length ≠ 0 := by
          intro h0
          exact hwl (by rw [← hrv, SimpleGraph.Walk.eq_of_length_eq_zero h0])
        rcases lt_trichotomy r' i with hcase | hcase | hcase
        · obtain ⟨v, hv₁, hv₂⟩ := IH (q₁.reverse.length + p.length) (by
            rw [SimpleGraph.Walk.length_reverse]; omega)
            r' i j k hcase hij hjk (by omega) q₁.reverse p (le_refl _)
            (by rw [walkTrace_reverse]; exact ht₁.trans hqd) hpd
          exact ⟨v, hv₂, hs₁ v (by rwa [SimpleGraph.Walk.support_reverse,
            List.mem_reverse] at hv₁)⟩
        · exact absurd hcase hri
        · rcases lt_trichotomy r' k with hcase2 | hcase2 | hcase2
          · obtain ⟨v, hv₁, hv₂⟩ := IH (p.length + q₂.length) (by omega)
              i r' k l hcase hcase2 hkl hl p q₂ (le_refl _) hpd (ht₂.trans hqd)
            exact ⟨v, hv₁, hs₂ v hv₂⟩
          · exact absurd hcase2 hrk
          · obtain ⟨v, hv₁, hv₂⟩ := IH (p.length + q₁.length) (by omega)
              i j k r' hij hjk hcase2 hrlt p q₁ (le_refl _) hpd (ht₁.trans hqd)
            exact ⟨v, hv₁, hs₁ v hv₂⟩
    · -- the first walk returns to the cycle: split it there
      rw [IsChord] at hcp
      push Not at hcp
      obtain ⟨w, hwp, hwγ, hwi, hwk⟩ := hcp
      by_cases hwq : w ∈ q.support
      · exact ⟨w, hwp, hwq⟩
      obtain ⟨r, hr, hrle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hwγ
      obtain ⟨r', hrv, hrlt⟩ : ∃ r' : ℕ, γ.getVert r' = w ∧ r' < γ.length := by
        by_cases hrz : r = γ.length
        · refine ⟨0, ?_, by omega⟩
          rw [SimpleGraph.Walk.getVert_zero, ← SimpleGraph.Walk.getVert_length γ, ← hrz]
          exact hr
        · exact ⟨r, hr, by omega⟩
      have hrj : r' ≠ j := by
        intro h
        exact hwq (by rw [← hrv, h]; exact q.start_mem_support)
      have hrl : r' ≠ l := by
        intro h
        exact hwq (by rw [← hrv, h]; exact q.end_mem_support)
      obtain ⟨p₁, p₂, hlen, hs₁, hs₂, ht₁, ht₂⟩ :=
        exists_split E p (show γ.getVert r' ∈ p.support by rw [hrv]; exact hwp)
      have hp₁len : p₁.length ≠ 0 := by
        intro h0
        exact hwi (by rw [← hrv, ← SimpleGraph.Walk.eq_of_length_eq_zero h0])
      have hp₂len : p₂.length ≠ 0 := by
        intro h0
        exact hwk (by rw [← hrv, SimpleGraph.Walk.eq_of_length_eq_zero h0])
      rcases lt_trichotomy r' j with hcase | hcase | hcase
      · obtain ⟨v, hv₁, hv₂⟩ := IH (p₂.length + q.length) (by omega)
          r' j k l hcase hjk hkl hl p₂ q (le_refl _) (ht₂.trans hpd) hqd
        exact ⟨v, hs₂ v hv₁, hv₂⟩
      · exact absurd hcase hrj
      · rcases lt_trichotomy r' l with hcase2 | hcase2 | hcase2
        · obtain ⟨v, hv₁, hv₂⟩ := IH (p₁.length + q.length) (by omega)
            i j r' l hij hcase hcase2 hl p₁ q (le_refl _) (ht₁.trans hpd) hqd
          exact ⟨v, hs₁ v hv₁, hv₂⟩
        · exact absurd hcase2 hrl
        · obtain ⟨v, hv₁, hv₂⟩ := IH (q.length + p₂.reverse.length) (by
            rw [SimpleGraph.Walk.length_reverse]; omega)
            j k l r' hjk hkl hcase2 hrlt q p₂.reverse (le_refl _) hqd
            (by rw [walkTrace_reverse]; exact ht₂.trans hpd)
          exact ⟨v, hs₂ v (by rwa [SimpleGraph.Walk.support_reverse,
            List.mem_reverse] at hv₂), hv₁⟩

end UCPlanar.Support
