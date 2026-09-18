/- Sign components of a harmonic function reach the boundary of a finite domain. -/
import UCPlanar.Support.Harmonic
import Mathlib

open scoped BigOperators Classical

namespace UCPlanar.Support

/-- **No finite nonempty set of vertices of a connected infinite graph is closed under
adjacency.** -/
theorem not_adjacency_closed {V : Type*} {G : SimpleGraph V} [Infinite V]
    (hG : G.Connected) (C : Finset V) (b : V) (hb : b ∈ C)
    (hclosed : ∀ w ∈ C, ∀ y, G.Adj w y → y ∈ C) : False := by
  classical
  have key : ∀ (u v : V), u ∈ C → G.Walk u v → v ∈ C := by
    intro u v hu p
    induction p with
    | nil => exact hu
    | @cons s t r h q ih => exact ih (hclosed s hu t h)
  have hall : ∀ v : V, v ∈ C := by
    intro v
    obtain ⟨p⟩ := hG.preconnected b v
    exact key b v hb p
  have hsub : (Set.univ : Set V) ⊆ (C : Set V) := by
    intro v _
    exact_mod_cast hall v
  exact (Set.infinite_univ (α := V)) (Set.Finite.subset C.finite_toSet hsub)

/-- **A positive vertex of a finite harmonic domain is joined to the boundary inside the positive
set.**  This is the maximum principle used in Step 3 of Section 3: a sign component of a vertex
where `f` does not vanish reaches a vertex adjacent to the complement of the domain. -/
theorem exists_positive_path_to_boundary {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    [Infinite V] (hG : G.Connected) {c : V → V → ℝ} (hc : LatticeProb.Network.IsCond G c)
    (S : Finset V) (f : V → ℝ)
    (hharm : ∀ x ∈ S, LatticeProb.Network.netLaplacian G c f x = 0)
    (x₀ : V) (hx₀ : x₀ ∈ S) (hpos : 0 < f x₀) :
    ∃ (w : V) (p : G.Walk x₀ w), (∀ z ∈ p.support, z ∈ S ∧ 0 < f z) ∧
      ∃ y, G.Adj w y ∧ y ∉ S := by
  classical
  by_contra hcon
  push Not at hcon
  set C : Finset V :=
    S.filter (fun w => ∃ p : G.Walk x₀ w, ∀ z ∈ p.support, z ∈ S ∧ 0 < f z) with hC
  have hx₀C : x₀ ∈ C := by
    rw [hC]
    refine Finset.mem_filter.mpr ⟨hx₀, ⟨SimpleGraph.Walk.nil, ?_⟩⟩
    intro z hz
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    subst hz
    exact ⟨hx₀, hpos⟩
  have hCpos : ∀ w ∈ C, 0 < f w := by
    intro w hw
    rw [hC] at hw
    obtain ⟨-, p, hp⟩ := Finset.mem_filter.mp hw
    exact (hp w p.end_mem_support).2
  obtain ⟨b, hbC, hbmax⟩ := Finset.exists_max_image C f ⟨x₀, hx₀C⟩
  have hfb : 0 < f b := hCpos b hbC
  set C' : Finset V := C.filter (fun w => f w = f b) with hC'
  have hbC' : b ∈ C' := by rw [hC']; exact Finset.mem_filter.mpr ⟨hbC, rfl⟩
  have hclosed : ∀ w ∈ C', ∀ y, G.Adj w y → y ∈ C' := by
    intro w hw y hwy
    rw [hC'] at hw
    obtain ⟨hwC, hwb⟩ := Finset.mem_filter.mp hw
    have hwC0 := hwC
    rw [hC] at hwC0
    obtain ⟨hwS, p, hp⟩ := Finset.mem_filter.mp hwC0
    have hmaxw : ∀ z, G.Adj w z → f z ≤ f w := by
      intro z hwz
      rw [hwb]
      by_cases hz : 0 < f z
      · have hzS : z ∈ S := hcon w p hp z hwz
        have hwalk : ∀ u ∈ (p.concat hwz).support, u ∈ S ∧ 0 < f u := by
          intro u hu
          simp only [SimpleGraph.Walk.support_concat,
            List.mem_append, List.mem_singleton] at hu
          rcases hu with hu | hu
          · exact hp u hu
          · subst hu; exact ⟨hzS, hz⟩
        have hzC : z ∈ C := by
          rw [hC]; exact Finset.mem_filter.mpr ⟨hzS, ⟨p.concat hwz, hwalk⟩⟩
        exact hbmax z hzC
      · push Not at hz
        linarith
    have heq := UCPlanar.Support.maximum_neighbors hc w (hharm w hwS) hmaxw y hwy
    have hyS : y ∈ S := hcon w p hp y hwy
    have hwalk : ∀ u ∈ (p.concat hwy).support, u ∈ S ∧ 0 < f u := by
      intro u hu
      simp only [SimpleGraph.Walk.support_concat,
        List.mem_append, List.mem_singleton] at hu
      rcases hu with hu | hu
      · exact hp u hu
      · subst hu; exact ⟨hyS, by rw [heq, hwb]; exact hfb⟩
    have hyC : y ∈ C := by
      rw [hC]; exact Finset.mem_filter.mpr ⟨hyS, ⟨p.concat hwy, hwalk⟩⟩
    rw [hC']
    exact Finset.mem_filter.mpr ⟨hyC, by rw [heq, hwb]⟩
  exact UCPlanar.Support.not_adjacency_closed hG C' b hbC' hclosed

end UCPlanar.Support
