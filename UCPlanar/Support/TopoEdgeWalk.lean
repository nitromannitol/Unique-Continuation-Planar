/- The drawing of a walk read as the drawing of the edges it uses. -/
import UCPlanar.Support.TopoMinimal
import Mathlib

open Set
open scoped Classical

namespace UCPlanar.Support

variable {V : Type*} {G : SimpleGraph V}

/-- A drawn edge lies in the drawing of the graph. -/
theorem arcOf_subset_trace (E : UCPlanar.PlaneEmbedding G) {e : Sym2 V} :
    E.arcOf e ⊆ E.trace := by
  rintro q ⟨x, y, h, -, hq⟩
  exact Or.inr ⟨x, y, h, hq⟩

/-- The drawing of a set of edges lies in the drawing of the graph. -/
theorem edgesTrace_subset_trace (E : UCPlanar.PlaneEmbedding G) (T : Set (Sym2 V)) :
    E.edgesTrace T ⊆ E.trace := by
  rintro q hq
  simp only [UCPlanar.PlaneEmbedding.edgesTrace, Set.mem_iUnion] at hq
  obtain ⟨e, -, hqe⟩ := hq
  exact arcOf_subset_trace E hqe

/-- **The drawing of a walk is carried by the edges it uses**, together with its starting
vertex, which the empty walk contributes. -/
theorem walkTrace_subset_edgesTrace (E : UCPlanar.PlaneEmbedding G) {x y : V}
    (γ : G.Walk x y) :
    E.walkTrace γ ⊆ E.edgesTrace {e | e ∈ γ.edges} ∪ {E.pos x} := by
  induction γ with
  | nil => intro q hq; exact Or.inr hq
  | @cons a b c h tail ih =>
    intro q hq
    have hfirst : E.arcOf s(a, b) ⊆ E.edgesTrace {e | e ∈ (SimpleGraph.Walk.cons h tail).edges} :=
      fun z hz => Set.mem_biUnion (by simp) hz
    rcases hq with hq | hq
    · exact Or.inl (hfirst (by rw [arcOf_eq E h]; exact hq))
    · rcases ih hq with hq' | hq'
      · refine Or.inl ?_
        simp only [UCPlanar.PlaneEmbedding.edgesTrace, Set.mem_iUnion, Set.mem_setOf_eq] at hq' ⊢
        obtain ⟨e, he, hqe⟩ := hq'
        exact ⟨e, by simp [he], hqe⟩
      · refine Or.inl (hfirst ?_)
        rw [arcOf_eq E h]
        simp only [Set.mem_singleton_iff] at hq'
        subst hq'
        exact ⟨1, (E.edge h).target⟩



/-- A walk of positive length is drawn inside the drawing of any edge set holding its edges:
its starting vertex is an end of its first edge. -/
theorem walkTrace_subset_edgesTrace_of_edges (E : UCPlanar.PlaneEmbedding G)
    {T : Set (Sym2 V)} {x y : V} (γ : G.Walk x y) (hγ : ∀ e ∈ γ.edges, e ∈ T)
    (hlen : γ.length ≠ 0) : E.walkTrace γ ⊆ E.edgesTrace T := by
  have hstart : E.pos x ∈ E.edgesTrace T := by
    cases γ with
    | nil => simp at hlen
    | @cons _ b _ h tail =>
      refine Set.mem_biUnion (hγ s(x, b) (by simp)) ?_
      rw [arcOf_eq E h]
      exact ⟨0, (E.edge h).source⟩
  intro q hq
  rcases walkTrace_subset_edgesTrace E γ hq with h | h
  · exact edgesTrace_mono E (fun e he => hγ e he) h
  · simp only [Set.mem_singleton_iff] at h
    subst h
    exact hstart

/-- **A cycle of an edge set separates no more than the set itself.**  Whatever a cycle drawn
from edges of `T` separates from infinity is separated by the drawing of `T`, unless it lies on
that drawing. -/
theorem insideOf_walkTrace_subset (E : UCPlanar.PlaneEmbedding G) {T : Finset (Sym2 V)}
    {o : V} (γ : G.Walk o o) (hγ : ∀ e ∈ γ.edges, e ∈ T) (hlen : γ.length ≠ 0) :
    insideOf (E.walkTrace γ) \ E.edgesTrace ↑T ⊆ insideOf (E.edgesTrace ↑T) :=
  insideOf_sdiff_subset
    (walkTrace_subset_edgesTrace_of_edges E γ (fun e he => by exact_mod_cast hγ e he) hlen)

end UCPlanar.Support
