/- Connectivity of an edge set with no splitting vertex. -/
import UCPlanar.Support.TopoEdgeWalk
import Mathlib

open Set
open scoped Classical

namespace UCPlanar.Support

variable {V : Type*} {G : SimpleGraph V}

/-- **An edge set with no splitting vertex is connected.**  If no partition of the edges into two
disjoint nonempty parts meets in at most one vertex, then every vertex of every edge is joined to
every other by a walk using only edges of the set.  The two parts are the edges the walks from a
fixed vertex reach and the edges they do not, which share no vertex at all, so the hypothesis
empties the second one. -/
theorem reachable_of_no_split {T : Finset (Sym2 V)}
    (hT : ↑T ⊆ G.edgeSet)
    (hsplit : ∀ T₁ T₂ : Finset (Sym2 V), T₁ ⊆ T → T₂ ⊆ T → (∀ e ∈ T, e ∈ T₁ ∨ e ∈ T₂) →
      Disjoint T₁ T₂ → ∀ v : V,
      (∀ z : V, (∃ e ∈ T₁, z ∈ e) → (∃ f ∈ T₂, z ∈ f) → z = v) → T₁ = ∅ ∨ T₂ = ∅)
    {z : V} {e₀ : Sym2 V} (he₀ : e₀ ∈ T) (hz : z ∈ e₀) :
    ∀ f ∈ T, ∀ y : V, y ∈ f → ∃ w : G.Walk z y, ∀ g ∈ w.edges, g ∈ T := by
  classical
  have hpair : ∀ (g : Sym2 V) (y y' : V), y ∈ g → y' ∈ g → y ≠ y' → g = s(y, y') := by
    refine Sym2.ind ?_
    intro a b y y' hy hy' hne
    rw [Sym2.mem_iff] at hy hy'
    rcases hy with rfl | rfl <;> rcases hy' with rfl | rfl
    · exact absurd rfl hne
    · rfl
    · exact Sym2.eq_swap
    · exact absurd rfl hne
  set R : Set V := {y | ∃ w : G.Walk z y, ∀ g ∈ w.edges, g ∈ T} with hRdef
  have hzR : z ∈ R := ⟨SimpleGraph.Walk.nil, by simp⟩
  have hstep : ∀ g ∈ T, ∀ y : V, y ∈ g → y ∈ R → ∀ y' : V, y' ∈ g → y' ∈ R := by
    intro g hg y hy hyR y' hy'
    by_cases hyy : y' = y
    · exact hyy ▸ hyR
    · have hgs : g = s(y, y') := hpair g y y' hy hy' (fun hc => hyy hc.symm)
      have hadj : G.Adj y y' := by
        have hge : g ∈ G.edgeSet := hT hg
        rw [hgs] at hge
        exact hge
      obtain ⟨w, hw⟩ := hyR
      refine ⟨w.concat hadj, ?_⟩
      intro q hq
      rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.mem_append] at hq
      rcases hq with h1 | h1
      · exact hw q h1
      · rw [List.mem_singleton] at h1
        rw [h1, ← hgs]
        exact hg
  have h1 : T.filter (fun g => ∃ y ∈ g, y ∈ R) ⊆ T := Finset.filter_subset _ _
  have h2 : T.filter (fun g => ¬ ∃ y ∈ g, y ∈ R) ⊆ T := Finset.filter_subset _ _
  have hcover : ∀ g ∈ T, g ∈ T.filter (fun g => ∃ y ∈ g, y ∈ R) ∨
      g ∈ T.filter (fun g => ¬ ∃ y ∈ g, y ∈ R) := by
    intro g hg
    by_cases hc : ∃ y ∈ g, y ∈ R
    · exact Or.inl (Finset.mem_filter.mpr ⟨hg, hc⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hg, hc⟩)
  have hdisj : Disjoint (T.filter (fun g => ∃ y ∈ g, y ∈ R))
      (T.filter (fun g => ¬ ∃ y ∈ g, y ∈ R)) := by
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    exact (Finset.mem_filter.mp hg2).2 (Finset.mem_filter.mp hg1).2
  have hmeet : ∀ w : V, (∃ g ∈ T.filter (fun g => ∃ y ∈ g, y ∈ R), w ∈ g) →
      (∃ h ∈ T.filter (fun g => ¬ ∃ y ∈ g, y ∈ R), w ∈ h) → w = z := by
    rintro w ⟨g, hg, hwg⟩ ⟨h, hh, hwh⟩
    exfalso
    obtain ⟨hgT, y, hyg, hyR⟩ := Finset.mem_filter.mp hg
    exact (Finset.mem_filter.mp hh).2 ⟨w, hwh, hstep g hgT y hyg hyR w hwg⟩
  rcases hsplit _ _ h1 h2 hcover hdisj z hmeet with hE | hE
  · exfalso
    have hmem : e₀ ∈ T.filter (fun g => ∃ y ∈ g, y ∈ R) :=
      Finset.mem_filter.mpr ⟨he₀, ⟨z, hz, hzR⟩⟩
    rw [hE] at hmem
    exact absurd hmem (Finset.notMem_empty _)
  · intro f hf y hy
    have hfT : f ∈ T.filter (fun g => ∃ y ∈ g, y ∈ R) := by
      rcases hcover f hf with h | h
      · exact h
      · rw [hE] at h
        exact absurd h (Finset.notMem_empty _)
    obtain ⟨-, y', hy', hy'R⟩ := Finset.mem_filter.mp hfT
    exact hstep f hf y' hy' hy'R y hy


/-- **A minimal separator is connected.**  The split lemma supplies the hypothesis of
`reachable_of_no_split` for an edge set no proper subset of which still separates the point. -/
theorem reachable_of_minimal (E : UCPlanar.PlaneEmbedding G) (hJ : E.EdgeSplitting)
    {T : Finset (Sym2 V)} (hT : ↑T ⊆ G.edgeSet) {p : UCPlanar.Plane}
    (hp : p ∈ insideOf (E.edgesTrace ↑T))
    (hmin : ∀ U : Finset (Sym2 V), U ⊂ T → p ∉ insideOf (E.edgesTrace ↑U))
    {z : V} {e₀ : Sym2 V} (he₀ : e₀ ∈ T) (hz : z ∈ e₀) :
    ∀ f ∈ T, ∀ y : V, y ∈ f → ∃ w : G.Walk z y, ∀ g ∈ w.edges, g ∈ T :=
  reachable_of_no_split hT
    (fun _ _ h1 h2 hcover hdisj _ hmeet =>
      eq_empty_of_split_of_minimal E hJ hT h1 h2 hcover hdisj hmeet hp hmin) he₀ hz

/-- The empty edge set separates nothing from infinity. -/
theorem insideOf_edgesTrace_empty (E : UCPlanar.PlaneEmbedding G) :
    insideOf (E.edgesTrace (∅ : Set (Sym2 V))) = ∅ := by
  have h : E.edgesTrace (∅ : Set (Sym2 V)) = (∅ : Set UCPlanar.Plane) := by
    simp [UCPlanar.PlaneEmbedding.edgesTrace]
  rw [h]
  exact insideOf_eq_empty_of_countable Set.countable_empty Bornology.isBounded_empty

/-- A separating edge set has an edge. -/
theorem nonempty_of_separating (E : UCPlanar.PlaneEmbedding G) {T : Finset (Sym2 V)}
    {p : UCPlanar.Plane} (hp : p ∈ insideOf (E.edgesTrace ↑T)) : T.Nonempty := by
  rcases Finset.eq_empty_or_nonempty T with rfl | h
  · rw [Finset.coe_empty, insideOf_edgesTrace_empty E] at hp
    exact absurd hp (Set.notMem_empty p)
  · exact h

end UCPlanar.Support
