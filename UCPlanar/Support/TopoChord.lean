/- Drawn chords of a drawn cycle: their traces meet the cycle only at their ends. -/
import UCPlanar.Support.TopoTransport

open Set

open scoped Classical

namespace UCPlanar.Support

/-- A drawn edge of a walk is drawn inside the walk. -/
theorem edge_range_subset_walkTrace {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {x y u v : V} (w : G.Walk x y) (h : G.Adj u v)
    (hm : s(u, v) ∈ w.edges) : Set.range (E.edge h) ⊆ E.walkTrace w := by
  induction w with
  | nil => simp at hm
  | @cons a c b hac tail ih =>
      rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at hm
      rw [UCPlanar.PlaneEmbedding.walkTrace]
      rcases hm with hm | hm
      · rw [Sym2.eq_iff] at hm
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Set.subset_union_of_subset_left (le_of_eq rfl) _
        · rw [E.edge_symm h]
          exact Set.subset_union_of_subset_left (le_of_eq rfl) _
      · exact Set.subset_union_of_subset_right (ih hm) _

/-- A walk whose edges and start lie in another walk is drawn inside it. -/
theorem walkTrace_mono_of_edges {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {x y x' y' : V} (w : G.Walk x y) (w' : G.Walk x' y')
    (hedges : ∀ e ∈ w.edges, e ∈ w'.edges) (hx : x ∈ w'.support) :
    E.walkTrace w ⊆ E.walkTrace w' := by
  induction w with
  | @nil a =>
      intro t ht
      have h1 : t = E.pos a := ht
      rw [h1]
      exact (E.pos_mem_walkTrace_iff w' a).mpr hx
  | @cons a c b hac tail ih =>
      rw [UCPlanar.PlaneEmbedding.walkTrace]
      have hmem : s(a, c) ∈ w'.edges := by
        refine hedges _ ?_
        rw [SimpleGraph.Walk.edges_cons]
        exact List.mem_cons_self
      refine Set.union_subset (edge_range_subset_walkTrace E w' hac hmem) ?_
      refine ih (fun e he => ?_) (SimpleGraph.Walk.snd_mem_support_of_mem_edges w' hmem)
      refine hedges e ?_
      rw [SimpleGraph.Walk.edges_cons]
      exact List.mem_cons_of_mem _ he

/-- The simple path extracted from a walk is drawn inside it. -/
theorem walkTrace_bypass_subset {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {x y : V} (w : G.Walk x y) :
    E.walkTrace w.bypass ⊆ E.walkTrace w :=
  walkTrace_mono_of_edges E w.bypass w
    (fun _ he => w.edges_bypass_subset_edges he) w.start_mem_support

/-- A walk is a chord of a cycle when it meets the cycle only at its two ends. -/
def IsChord {V : Type*} {G : SimpleGraph V} {o x y : V}
    (γ : G.Walk o o) (w : G.Walk x y) : Prop :=
  ∀ v ∈ w.support, v ∈ γ.support → v = x ∨ v = y

/-- A chord of a cycle is drawn meeting the cycle only in its two drawn ends. -/
theorem chord_trace_inter_subset {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {o x y : V} (γ : G.Walk o o) (w : G.Walk x y)
    (hch : IsChord γ w) (hxy : s(x, y) ∉ γ.edges) :
    E.walkTrace w ∩ E.walkTrace γ ⊆ ({E.pos x, E.pos y} : Set UCPlanar.Plane) := by
  intro t ht
  by_cases htv : t ∈ Set.range E.pos
  · obtain ⟨v, rfl⟩ := htv
    have hw : v ∈ w.support := (E.pos_mem_walkTrace_iff w v).mp ht.1
    have hg : v ∈ γ.support := (E.pos_mem_walkTrace_iff γ v).mp ht.2
    rcases hch v hw hg with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · obtain ⟨u₁, v₁, h₁, ht₁, hu₁, hv₁, he₁⟩ :=
      exists_edge_of_mem_walkTrace_edges E w ht.1 htv
    obtain ⟨u₂, v₂, h₂, ht₂, hu₂, hv₂, he₂⟩ :=
      exists_edge_of_mem_walkTrace_edges E γ ht.2 htv
    rcases edge_range_inter_or_eq E h₁ h₂ with hsub | hcase
    · rcases hsub ⟨ht₁, ht₂⟩ with h | h
      · exact absurd ⟨u₁, h.symm⟩ htv
      · exact absurd ⟨v₁, h.symm⟩ htv
    · exfalso
      have hsame : s(u₁, v₁) ∈ γ.edges := by
        rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact he₂
        · rwa [Sym2.eq_swap] at he₂
      have hgu : u₁ ∈ γ.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges γ hsame
      have hgv : v₁ ∈ γ.support := SimpleGraph.Walk.snd_mem_support_of_mem_edges γ hsame
      have hcu := hch u₁ hu₁ hgu
      have hcv := hch v₁ hv₁ hgv
      have hne : u₁ ≠ v₁ := h₁.ne
      rcases hcu with rfl | rfl <;> rcases hcv with h' | h'
      · exact hne h'.symm
      · exact hxy (h' ▸ hsame)
      · exact hxy (by rw [Sym2.eq_swap]; exact h' ▸ hsame)
      · exact hne h'.symm

/-- A chord of a cycle drawn in the closed cycle domain has its interior strictly inside. -/
theorem chord_trace_diff_subset_inside {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {o x y : V} (γ : G.Walk o o) (w : G.Walk x y)
    (hch : IsChord γ w) (hxy : s(x, y) ∉ γ.edges)
    (hsub : E.walkTrace w ⊆ E.closedCycleDomain γ) :
    E.walkTrace w \ ({E.pos x, E.pos y} : Set UCPlanar.Plane) ⊆ insideOf (E.walkTrace γ) := by
  intro t ht
  have hnot : t ∉ E.walkTrace γ := fun hg =>
    ht.2 (chord_trace_inter_subset E γ w hch hxy ⟨ht.1, hg⟩)
  rcases hsub ht.1 with hg | hg
  · exact absurd hg hnot
  · exact hg

end UCPlanar.Support
