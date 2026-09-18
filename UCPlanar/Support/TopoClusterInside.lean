/- The filled cluster lies inside the cycle that bounds it: a connected set disjoint from a
drawn cycle is enclosed by it as soon as one of its points is. -/
import UCPlanar.Support.TopoFaceCluster
import UCPlanar.Support.TopoBounded
import Mathlib

open Set

namespace UCPlanar.Support

/-- **A connected set disjoint from a set lies inside it as soon as one of its points does.**
The set is contained in a single complementary component, and that component is the bounded one
through the given point. -/
theorem subset_insideOf_of_isPreconnected {X : Type*} [TopologicalSpace X] [Bornology X]
    {J S : Set X} {p : X} (hS : IsPreconnected S) (hp : p ∈ S) (hdisj : S ⊆ Jᶜ)
    (hpin : p ∈ insideOf J) : S ⊆ insideOf J := by
  intro q hq
  have hsub : S ⊆ connectedComponentIn Jᶜ p := hS.subset_connectedComponentIn hp hdisj
  have hq' : q ∈ connectedComponentIn Jᶜ p := hsub hq
  refine ⟨hdisj hq, ?_⟩
  rw [← connectedComponentIn_eq hq']
  exact hpin.2

/-- **The unbounded complementary components form an open set.**  Each of them is an open
neighbourhood of each of its points, so the region a closed set encloses, together with the set
itself, is closed. -/
theorem isClosed_insideOf_union {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    [Bornology X] {J : Set X} (hJ : IsClosed J) : IsClosed (insideOf J ∪ J) := by
  refine ⟨?_⟩
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hxJ : x ∉ J := fun h => hx (Or.inr h)
  have hub : ¬ Bornology.IsBounded (connectedComponentIn Jᶜ x) := fun h => hx (Or.inl ⟨hxJ, h⟩)
  have hopen : IsOpen (connectedComponentIn Jᶜ x) := hJ.isOpen_compl.connectedComponentIn
  refine Filter.mem_of_superset (hopen.mem_nhds (mem_connectedComponentIn hxJ)) ?_
  intro y hy
  have hyJ : y ∈ Jᶜ := connectedComponentIn_subset _ _ hy
  have heq : connectedComponentIn Jᶜ x = connectedComponentIn Jᶜ y := connectedComponentIn_eq hy
  intro hmem
  rcases hmem with ⟨-, hb⟩ | hJy
  · exact hub (by rw [heq]; exact hb)
  · exact hyJ hJy

variable {V : Type*} {G : SimpleGraph V}

/-- **The closed region a drawn closed walk bounds is closed.** -/
theorem isClosed_closedCycleDomain (E : UCPlanar.PlaneEmbedding G) {o : V} (γ : G.Walk o o) :
    IsClosed (E.closedCycleDomain γ) := by
  rw [closedCycleDomain_eq_union, Set.union_comm]
  exact isClosed_insideOf_union (E.isCompact_walkTrace γ).isClosed

/-- **A face incident to a vertex of `N` lies in the filled region.**  Distinct faces are
disjoint open sets, so such a face meets the closure of no face avoiding `N`. -/
theorem isFace_subset_clusterRegion (Q : UCPlanar.PeriodicPlaneGraph V)
    (hLF : Q.embedding.LocallyFiniteFaces) {N : Set V} {F : Set UCPlanar.Plane}
    (hF : Q.embedding.IsFace F) {x : V} (hx : x ∈ N) (hinc : Q.embedding.Incident F x) :
    F ⊆ Q.embedding.clusterRegion N := by
  intro p hp
  rw [mem_clusterRegion_iff Q.embedding hLF]
  intro F' hF' hcl
  have hne : F ≠ F' := by
    intro h
    exact hF'.2 x (h ▸ hinc) hx
  have hdis : Disjoint F F' := (isFace_eq_or_disjoint Q.embedding hF hF'.1).resolve_left hne
  have hop : IsOpen F := isOpen_isFace Q hF
  have hnb : F ∈ nhds p := hop.mem_nhds hp
  obtain ⟨q, hqF, hqF'⟩ := (mem_closure_iff_nhds.mp hcl) F hnb
  exact Set.disjoint_left.mp hdis hqF hqF'

/-- **The filled cluster through a vertex is enclosed by any cycle drawn on its frontier.**
The component of the filled region through the drawn vertex is connected and misses the drawing
of the cycle, so it lies in the same complementary component as that vertex. -/
theorem connectedComponentIn_clusterRegion_subset_insideOf (E : UCPlanar.PlaneEmbedding G)
    {N : Set V} {p : UCPlanar.Plane} (hp : p ∈ E.clusterRegion N) {b : V} {γ : G.Walk b b}
    (hγ : E.walkTrace γ ⊆ frontier (E.clusterRegion N))
    (hin : p ∈ insideOf (E.walkTrace γ)) :
    connectedComponentIn (E.clusterRegion N) p ⊆ insideOf (E.walkTrace γ) := by
  refine subset_insideOf_of_isPreconnected isPreconnected_connectedComponentIn
    (mem_connectedComponentIn hp) ?_ hin
  intro q hq hq2
  have hq1 : q ∈ E.clusterRegion N := connectedComponentIn_subset _ _ hq
  have hq3 : q ∈ frontier (E.clusterRegion N) := hγ hq2
  have hdis : E.clusterRegion N ∩ frontier (E.clusterRegion N) = ∅ :=
    (isOpen_clusterRegion E N).inter_frontier_eq
  have hmem : q ∈ E.clusterRegion N ∩ frontier (E.clusterRegion N) := ⟨hq1, hq3⟩
  rw [hdis] at hmem
  exact hmem

/-- **The closed filled cluster is enclosed by the cycle.** -/
theorem closure_connectedComponentIn_clusterRegion_subset (E : UCPlanar.PlaneEmbedding G)
    {N : Set V} {p : UCPlanar.Plane} (hp : p ∈ E.clusterRegion N) {b : V} {γ : G.Walk b b}
    (hγ : E.walkTrace γ ⊆ frontier (E.clusterRegion N))
    (hin : p ∈ insideOf (E.walkTrace γ)) :
    closure (connectedComponentIn (E.clusterRegion N) p) ⊆ E.closedCycleDomain γ := by
  refine closure_minimal ?_ (isClosed_closedCycleDomain E γ)
  intro q hq
  exact Or.inr (connectedComponentIn_clusterRegion_subset_insideOf E hp hγ hin hq)

/-- **A vertex drawn in the closed filled cluster is enclosed by the cycle.** -/
theorem mem_cycleRegion_of_pos_mem_closure (E : UCPlanar.PlaneEmbedding G)
    {N : Set V} {p : UCPlanar.Plane} (hp : p ∈ E.clusterRegion N) {b : V} {γ : G.Walk b b}
    (hγ : E.walkTrace γ ⊆ frontier (E.clusterRegion N))
    (hin : p ∈ insideOf (E.walkTrace γ)) {z : V}
    (hz : E.pos z ∈ closure (connectedComponentIn (E.clusterRegion N) p)) :
    z ∈ E.cycleRegion γ := by
  rw [← E.pos_mem_closedCycleDomain_iff γ z]
  exact closure_connectedComponentIn_clusterRegion_subset E hp hγ hin hz

/-- **The cycle surrounding the cluster encloses the whole filled cluster.**  Together with the
properties of the surrounding cycle, every vertex drawn in the closure of the filled region
through `x₀` lies in the plane region the cycle bounds.  This is the enclosure the maximum
principle step of Step 3 asks for. -/
theorem exists_surrounding_cycle_enclosing (E : UCPlanar.PlaneEmbedding G)
    (hbc : E.HasBoundaryCycles) (hLF : E.LocallyFiniteFaces) {N : Set V} {x₀ : V} (hx₀ : x₀ ∈ N)
    (hbdd : Bornology.IsBounded (E.clusterRegion N))
    {T : Finset (Sym2 V)} (hT : ↑T ⊆ G.edgeSet)
    (hcover : frontier (E.clusterRegion N) ⊆ E.edgesTrace ↑T)
    (harc : ∀ e ∈ T, E.arcOf e ⊆ frontier (E.clusterRegion N)) :
    ∃ (b : V) (γ : G.Walk b b), γ.IsCycle ∧ x₀ ∈ E.cycleRegion γ ∧
      (∀ z ∈ γ.support, z ∉ N) ∧
      (∀ z ∈ γ.support, ∃ F ∈ E.facesAvoiding N, E.Incident F z) ∧
      ∀ z : V, E.pos z ∈ closure (connectedComponentIn (E.clusterRegion N) (E.pos x₀)) →
        z ∈ E.cycleRegion γ := by
  obtain ⟨b, γ, hcyc, _, hreg, hout, hinc, hin, hwt⟩ :=
    exists_surrounding_cycle E hbc hLF hx₀ hbdd hT hcover harc
  refine ⟨b, γ, hcyc, hreg, hout, hinc, ?_⟩
  intro z hz
  exact mem_cycleRegion_of_pos_mem_closure E (pos_mem_clusterRegion E hLF hx₀) hwt hin hz

end UCPlanar.Support
