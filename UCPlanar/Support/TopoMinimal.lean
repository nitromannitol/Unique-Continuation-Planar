/- The boundary cycle theorem: every finite edge set whose drawing separates a point of the
plane from infinity carries a cycle that already separates it, reduced to Janiszewski's theorem
at a single point and to the two connected base case. -/
import UCPlanar.Support.TopoEdgeSet
import Mathlib

open Set
open scoped Classical

/-- **The boundary cycle property.**  Whenever the drawing of a finite set of edges of `G`
separates a point of the plane from infinity, some cycle of `G` built from those edges already
separates that point from infinity. -/
def UCPlanar.PlaneEmbedding.HasBoundaryCycles {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) : Prop :=
  ∀ T : Finset (Sym2 V), ↑T ⊆ G.edgeSet → ∀ p : UCPlanar.Plane,
    p ∈ UCPlanar.Support.insideOf (E.edgesTrace ↑T) →
      ∃ (b : V) (γ : G.Walk b b), γ.IsCycle ∧ (∀ e ∈ γ.edges, e ∈ T) ∧
        p ∈ UCPlanar.Support.insideOf (E.walkTrace γ)

/-- **Janiszewski's theorem at a single point, in the vocabulary of the embedding.**  When the
drawings of two disjoint edge sets meet in at most one vertex, a point their union separates
from infinity is already separated by one of them.  This is the only consequence of the
classical unicoherence statement that the boundary cycle theorem uses, and unlike the statement
for arbitrary closed sets it speaks only about finite plane graphs. -/
def UCPlanar.PlaneEmbedding.EdgeSplitting {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) : Prop :=
  ∀ T₁ T₂ : Finset (Sym2 V), ↑T₁ ⊆ G.edgeSet → ↑T₂ ⊆ G.edgeSet → Disjoint T₁ T₂ →
    ∀ v : V, (∀ z : V, (∃ e ∈ T₁, z ∈ e) → (∃ f ∈ T₂, z ∈ f) → z = v) →
    ∀ p : UCPlanar.Plane, p ∈ UCPlanar.Support.insideOf (E.edgesTrace ↑(T₁ ∪ T₂)) →
      p ∈ UCPlanar.Support.insideOf (E.edgesTrace ↑T₁) ∨
        p ∈ UCPlanar.Support.insideOf (E.edgesTrace ↑T₂)

namespace UCPlanar.Support

variable {V : Type*} {G : SimpleGraph V}

/-- **Reduction to a minimal separator.**  To prove the boundary cycle property it is enough
to produce the cycle when no proper subset of the edge set still separates the point: a set that
is not minimal is replaced by a smaller separating subset, and the cycle that subset carries is a
cycle of the original set. -/
theorem hasBoundaryCycles_of_minimal (E : UCPlanar.PlaneEmbedding G)
    (h : ∀ T : Finset (Sym2 V), ↑T ⊆ G.edgeSet → ∀ p : UCPlanar.Plane,
      p ∈ insideOf (E.edgesTrace ↑T) →
      (∀ U : Finset (Sym2 V), U ⊂ T → p ∉ insideOf (E.edgesTrace ↑U)) →
      ∃ (b : V) (γ : G.Walk b b), γ.IsCycle ∧ (∀ e ∈ γ.edges, e ∈ T) ∧
        p ∈ insideOf (E.walkTrace γ)) :
    E.HasBoundaryCycles := by
  classical
  intro T
  induction T using Finset.strongInduction with
  | _ T ih =>
    intro hT p hp
    by_cases hmin : ∀ U : Finset (Sym2 V), U ⊂ T → p ∉ insideOf (E.edgesTrace ↑U)
    · exact h T hT p hp hmin
    · rcases Classical.not_forall.mp hmin with ⟨U, hU⟩
      rcases Classical.not_imp.mp hU with ⟨hUT, hpU⟩
      rw [Classical.not_not] at hpU
      obtain ⟨b, γ, hcyc, hedges, hin⟩ :=
        ih U hUT ((Finset.coe_subset.mpr hUT.le).trans hT) p hpU
      exact ⟨b, γ, hcyc, fun e he => hUT.le (hedges e he), hin⟩

/-- **Janiszewski's theorem at a point gives the splitting of an edge set.**  The drawings of
two finite edge sets are compact, hence closed, and two edge sets sharing a single vertex have
drawings meeting only at that vertex. -/
theorem edgeSplitting_of_janiszewskiPoint (hJ : JaniszewskiPoint)
    (E : UCPlanar.PlaneEmbedding G) : E.EdgeSplitting := by
  classical
  intro T₁ T₂ h1 h2 hdisj v hmeet p hp
  have hcl1 : IsClosed (E.edgesTrace ↑T₁) := (isCompact_edgesTrace E T₁.finite_toSet h1).isClosed
  have hcl2 : IsClosed (E.edgesTrace ↑T₂) := (isCompact_edgesTrace E T₂.finite_toSet h2).isClosed
  have hint : E.edgesTrace ↑T₁ ∩ E.edgesTrace ↑T₂ ⊆ {E.pos v} :=
    edgesTrace_inter_subset E h1 h2 (Finset.disjoint_coe.mpr hdisj)
      (fun z hz1 hz2 => hmeet z (by simpa using hz1) (by simpa using hz2))
  have hun : E.edgesTrace ↑(T₁ ∪ T₂) = E.edgesTrace ↑T₁ ∪ E.edgesTrace ↑T₂ := by
    rw [Finset.coe_union, edgesTrace_union]
  rw [hun] at hp
  exact insideOf_union_split hJ hcl1 hcl2 hint hp

/-- **A minimal separator does not split at a single vertex.**  If the edges of a minimal
separating set fall into two disjoint parts whose drawings meet only at one vertex, then one of
the parts is empty.  This is Janiszewski's theorem read on the two parts: were both nonempty,
each would be a proper subset, and the theorem puts the point inside one of them. -/
theorem eq_empty_of_split_of_minimal (E : UCPlanar.PlaneEmbedding G) (hJ : E.EdgeSplitting)
    {T T₁ T₂ : Finset (Sym2 V)} (hT : ↑T ⊆ G.edgeSet)
    (h1 : T₁ ⊆ T) (h2 : T₂ ⊆ T) (hcover : ∀ e ∈ T, e ∈ T₁ ∨ e ∈ T₂) (hdisj : Disjoint T₁ T₂)
    {v : V} (hmeet : ∀ z : V, (∃ e ∈ T₁, z ∈ e) → (∃ f ∈ T₂, z ∈ f) → z = v)
    {p : UCPlanar.Plane} (hp : p ∈ insideOf (E.edgesTrace ↑T))
    (hmin : ∀ U : Finset (Sym2 V), U ⊂ T → p ∉ insideOf (E.edgesTrace ↑U)) :
    T₁ = ∅ ∨ T₂ = ∅ := by
  classical
  rcases Finset.eq_empty_or_nonempty T₁ with hE | ⟨e₁, he₁⟩
  · exact Or.inl hE
  rcases Finset.eq_empty_or_nonempty T₂ with hE | ⟨e₂, he₂⟩
  · exact Or.inr hE
  exfalso
  have hTsub1 : (↑T₁ : Set (Sym2 V)) ⊆ G.edgeSet := (Finset.coe_subset.mpr h1).trans hT
  have hTsub2 : (↑T₂ : Set (Sym2 V)) ⊆ G.edgeSet := (Finset.coe_subset.mpr h2).trans hT
  have hTU : T₁ ∪ T₂ = T :=
    Finset.Subset.antisymm (Finset.union_subset h1 h2)
      (fun e he => Finset.mem_union.mpr (hcover e he))
  have hp' : p ∈ insideOf (E.edgesTrace ↑(T₁ ∪ T₂)) := by rw [hTU]; exact hp
  rcases hJ T₁ T₂ hTsub1 hTsub2 hdisj v hmeet p hp' with hin | hin
  · exact hmin T₁ ((Finset.ssubset_iff_of_subset h1).mpr
      ⟨e₂, h2 he₂, Finset.disjoint_right.mp hdisj he₂⟩) hin
  · exact hmin T₂ ((Finset.ssubset_iff_of_subset h2).mpr
      ⟨e₁, h1 he₁, Finset.disjoint_left.mp hdisj he₁⟩) hin

/-- **A minimal separator carries a second edge at each of its vertices.**  An edge with a free
end splits the set into that edge and the rest, two parts whose drawings meet only at the edge's
other end; the split lemma then leaves the single edge, whose drawing is a simple arc and
separates nothing. -/
theorem exists_other_edge_of_minimal (E : UCPlanar.PlaneEmbedding G)
    (hJ : E.EdgeSplitting)
    {T : Finset (Sym2 V)} (hT : ↑T ⊆ G.edgeSet) {p : UCPlanar.Plane}
    (hp : p ∈ insideOf (E.edgesTrace ↑T))
    (hmin : ∀ U : Finset (Sym2 V), U ⊂ T → p ∉ insideOf (E.edgesTrace ↑U)) :
    ∀ e ∈ T, ∀ z : V, z ∈ e → ∃ f ∈ T, f ≠ e ∧ z ∈ f := by
  classical
  have key : ∀ e : Sym2 V, ∀ z : V, z ∈ e → ∃ u : V, ∀ w : V, w ∈ e → w ≠ z → w = u := by
    refine Sym2.ind ?_
    intro x y z hz
    rw [Sym2.mem_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨y, fun w hw hwz => by rw [Sym2.mem_iff] at hw; tauto⟩
    · exact ⟨x, fun w hw hwz => by rw [Sym2.mem_iff] at hw; tauto⟩
  intro e he z hz
  by_contra hcon
  have hno : ∀ f ∈ T, f ≠ e → z ∉ f := fun f hf hfe hzf => hcon ⟨f, hf, hfe, hzf⟩
  obtain ⟨u, hu⟩ := key e z hz
  have h1 : ({e} : Finset (Sym2 V)) ⊆ T := Finset.singleton_subset_iff.mpr he
  have h2 : T.erase e ⊆ T := Finset.erase_subset _ _
  have hcover : ∀ f ∈ T, f ∈ ({e} : Finset (Sym2 V)) ∨ f ∈ T.erase e := by
    intro f hf
    by_cases hfe : f = e
    · exact Or.inl (Finset.mem_singleton.mpr hfe)
    · exact Or.inr (Finset.mem_erase.mpr ⟨hfe, hf⟩)
  have hdisj : Disjoint ({e} : Finset (Sym2 V)) (T.erase e) := by
    simp [Finset.disjoint_singleton_left]
  have hmeet : ∀ w : V, (∃ f ∈ ({e} : Finset (Sym2 V)), w ∈ f) →
      (∃ g ∈ T.erase e, w ∈ g) → w = u := by
    rintro w ⟨f, hf, hwf⟩ ⟨g, hg, hwg⟩
    have hfe : f = e := Finset.mem_singleton.mp hf
    subst hfe
    have hwz : w ≠ z := by
      rintro rfl
      exact hno g (h2 hg) (Finset.mem_erase.mp hg).1 hwg
    exact hu w hwf hwz
  rcases eq_empty_of_split_of_minimal E hJ hT h1 h2 hcover hdisj hmeet hp hmin with hE | hE
  · exact absurd hE (by simp)
  · have hTe : T = {e} := by
      rcases (Finset.erase_eq_empty_iff T e).mp hE with hnil | hsing
      · exact absurd he (by simp [hnil])
      · exact hsing
    rw [hTe] at hp
    have harc : E.edgesTrace (↑({e} : Finset (Sym2 V))) = E.arcOf e := by
      simp [UCPlanar.PlaneEmbedding.edgesTrace]
    rw [harc, insideOf_arcOf E (hT he)] at hp
    exact hp

end UCPlanar.Support

/-- **The two connected base case of the boundary cycle theorem.**  An edge set carrying a second
edge at each of its vertices and admitting no splitting vertex has, around every point its
drawing separates from infinity, a cycle of its own edges that already separates that point. -/
def UCPlanar.PlaneEmbedding.TwoConnectedBoundaryCycles {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) : Prop :=
  ∀ T : Finset (Sym2 V), ↑T ⊆ G.edgeSet →
    (∀ e ∈ T, ∀ z : V, z ∈ e → ∃ f ∈ T, f ≠ e ∧ z ∈ f) →
    (∀ T₁ T₂ : Finset (Sym2 V), T₁ ⊆ T → T₂ ⊆ T → (∀ e ∈ T, e ∈ T₁ ∨ e ∈ T₂) →
      Disjoint T₁ T₂ → ∀ v : V,
      (∀ z : V, (∃ e ∈ T₁, z ∈ e) → (∃ f ∈ T₂, z ∈ f) → z = v) → T₁ = ∅ ∨ T₂ = ∅) →
    ∀ p : UCPlanar.Plane, p ∈ UCPlanar.Support.insideOf (E.edgesTrace ↑T) →
      ∃ (b : V) (γ : G.Walk b b), γ.IsCycle ∧ (∀ e ∈ γ.edges, e ∈ T) ∧
        p ∈ UCPlanar.Support.insideOf (E.walkTrace γ)

namespace UCPlanar.Support

variable {V : Type*} {G : SimpleGraph V}

/-- **The boundary cycle theorem, reduced to two classical inputs.**  Granting Janiszewski's
theorem at a single point and the two connected base case, every finite edge set whose drawing
separates a point of the plane from infinity carries a cycle that separates it. -/
theorem hasBoundaryCycles_of_twoConnected (E : UCPlanar.PlaneEmbedding G)
    (hJ : E.EdgeSplitting) (hbase : E.TwoConnectedBoundaryCycles) :
    E.HasBoundaryCycles := by
  refine hasBoundaryCycles_of_minimal E ?_
  intro T hT p hp hmin
  refine hbase T hT (exists_other_edge_of_minimal E hJ hT hp hmin) ?_ p hp
  intro T₁ T₂ h1 h2 hcover hdisj v hmeet
  exact eq_empty_of_split_of_minimal E hJ hT h1 h2 hcover hdisj hmeet hp hmin

/-- A vertex drawn inside the region a closed walk encloses lies in that region. -/
theorem mem_cycleRegion_of_insideOf (E : UCPlanar.PlaneEmbedding G) {o x : V} (γ : G.Walk o o)
    (h : E.pos x ∈ insideOf (E.walkTrace γ)) : x ∈ E.cycleRegion γ :=
  Or.inr h

/-- **The boundary cycle theorem, read at a vertex.**  A vertex whose drawing is separated from
infinity by the drawing of a finite edge set lies in the region enclosed by a cycle of that
set. -/
theorem exists_cycle_region (E : UCPlanar.PlaneEmbedding G) (h : E.HasBoundaryCycles)
    {T : Finset (Sym2 V)} (hT : ↑T ⊆ G.edgeSet) {x₀ : V}
    (hx : E.pos x₀ ∈ insideOf (E.edgesTrace ↑T)) :
    ∃ (b : V) (γ : G.Walk b b), γ.IsCycle ∧ (∀ e ∈ γ.edges, e ∈ T) ∧ x₀ ∈ E.cycleRegion γ := by
  obtain ⟨b, γ, hcyc, hedges, hin⟩ := h T hT (E.pos x₀) hx
  exact ⟨b, γ, hcyc, hedges, mem_cycleRegion_of_insideOf E γ hin⟩

end UCPlanar.Support
