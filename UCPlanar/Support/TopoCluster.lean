/- The boundary cycle of a cluster: a bounded open plane region whose frontier is covered by the
drawing of a finite edge set is enclosed by a cycle of that edge set, drawn on that frontier. -/
import UCPlanar.Support.TopoEdgeWalk
import Mathlib

open Set
open scoped Classical

namespace UCPlanar.Support

/-- **A bounded open set with frontier inside a closed set lies inside that set.**  The connected
component of the complement through an interior point cannot leave the open set without meeting
its frontier, so it is contained in the open set and is bounded. -/
theorem insideOf_of_frontier_subset {X : Type*} [TopologicalSpace X] [Bornology X]
    {Ω S : Set X} {p : X} (hop : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hp : p ∈ Ω) (hfr : frontier Ω ⊆ S) (hpS : p ∉ S) :
    p ∈ insideOf S := by
  refine ⟨hpS, hb.subset ?_⟩
  have hpc : p ∈ Sᶜ := hpS
  have hsub : connectedComponentIn Sᶜ p ⊆ Sᶜ := connectedComponentIn_subset _ _
  have hconn : IsPreconnected (connectedComponentIn Sᶜ p) := isPreconnected_connectedComponentIn
  have hmem : p ∈ connectedComponentIn Sᶜ p := mem_connectedComponentIn hpc
  have hcover : connectedComponentIn Sᶜ p ⊆ Ω ∪ (closure Ω)ᶜ := by
    intro x hx
    by_cases hcl : x ∈ closure Ω
    · left
      have hnf : x ∉ frontier Ω := fun hf => hsub hx (hfr hf)
      rw [hop.frontier_eq] at hnf
      simpa [hcl] using hnf
    · exact Or.inr hcl
  refine hconn.subset_left_of_subset_union hop isClosed_closure.isOpen_compl ?_ hcover ⟨p, hmem, hp⟩
  exact Set.disjoint_compl_right_iff_subset.mpr subset_closure

/-- The frontier of a connected component of an open set is part of the frontier of that set. -/
theorem frontier_connectedComponentIn_subset {X : Type*} [TopologicalSpace X]
    [LocallyConnectedSpace X] {U : Set X} (hU : IsOpen U) (p : X) :
    frontier (connectedComponentIn U p) ⊆ frontier U := by
  intro x hx
  have hopen : IsOpen (connectedComponentIn U p) := hU.connectedComponentIn
  have hx' := hx
  rw [hopen.frontier_eq] at hx'
  have hclx : x ∈ closure (connectedComponentIn U p) := hx'.1
  have hnotx : x ∉ connectedComponentIn U p := hx'.2
  have hxU : x ∉ U := by
    intro hxU
    have hnb : connectedComponentIn U x ∈ nhds x :=
      (hU.connectedComponentIn).mem_nhds (mem_connectedComponentIn hxU)
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff_nhds.mp hclx _ hnb
    have e1 : connectedComponentIn U x = connectedComponentIn U y := connectedComponentIn_eq hy1
    have e2 : connectedComponentIn U p = connectedComponentIn U y := connectedComponentIn_eq hy2
    exact hnotx (by rw [e2, ← e1]; exact mem_connectedComponentIn hxU)
  have hclU : x ∈ closure U := closure_mono (connectedComponentIn_subset U p) hclx
  rw [hU.frontier_eq]
  exact ⟨hclU, hxU⟩

/-- A vertex of a walk of positive length lies on one of the walk's edges. -/
theorem exists_mem_edges_of_mem_support {V : Type*} {G : SimpleGraph V} {u v : V}
    (w : G.Walk u v) (hw : w.length ≠ 0) {z : V} (hz : z ∈ w.support) :
    ∃ e ∈ w.edges, z ∈ e := by
  induction w with
  | nil => simp at hw
  | @cons a b c h tail ih =>
    rw [SimpleGraph.Walk.edges_cons]
    rcases eq_or_ne z a with rfl | hza
    · exact ⟨s(z, b), List.mem_cons_self, by simp⟩
    · have hz' : z ∈ tail.support := by
        rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
        exact hz.resolve_left hza
      by_cases htail : tail.length = 0
      · have hlen : tail.support.length = 1 := by
          rw [SimpleGraph.Walk.length_support, htail]
        have hb : b ∈ tail.support := SimpleGraph.Walk.start_mem_support tail
        have hzb : z = b := by
          obtain ⟨w0, hw0⟩ := List.length_eq_one_iff.mp hlen
          rw [hw0] at hz' hb
          simp at hz' hb
          rw [hz', hb]
        exact ⟨s(a, b), List.mem_cons_self, by rw [hzb]; simp⟩
      · obtain ⟨e, he, hze⟩ := ih htail hz'
        exact ⟨e, List.mem_cons_of_mem _ he, hze⟩

variable {V : Type*} {G : SimpleGraph V}

/-- A point of the drawing of an edge set lies on one of its arcs. -/
theorem exists_arcOf_of_mem_edgesTrace (E : UCPlanar.PlaneEmbedding G) {T : Set (Sym2 V)}
    {p : UCPlanar.Plane} (hp : p ∈ E.edgesTrace T) : ∃ e ∈ T, p ∈ E.arcOf e := by
  simpa [UCPlanar.PlaneEmbedding.edgesTrace] using hp

/-- **The boundary cycle of a cluster.**  Let `Ω` be a bounded open region of the plane holding
the drawing of a vertex `x₀`, and let `T` be a finite set of edges whose arcs all lie on the
frontier of `Ω` and whose drawing covers that frontier.  Then a cycle of `T` encloses `x₀`, its
whole drawing lies on the frontier of `Ω`, and `x₀` is drawn in the plane region it bounds. -/
theorem exists_cluster_cycle (E : UCPlanar.PlaneEmbedding G)
    (hbc : E.HasBoundaryCycles) {Ω : Set UCPlanar.Plane} (hop : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) {x₀ : V} (hx : E.pos x₀ ∈ Ω)
    {T : Finset (Sym2 V)} (hT : ↑T ⊆ G.edgeSet)
    (hcover : frontier Ω ⊆ E.edgesTrace ↑T)
    (harc : ∀ e ∈ T, E.arcOf e ⊆ frontier Ω) :
    ∃ (b : V) (γ : G.Walk b b), γ.IsCycle ∧ (∀ e ∈ γ.edges, e ∈ T) ∧
      x₀ ∈ E.cycleRegion γ ∧ (∀ z ∈ γ.support, E.pos z ∈ frontier Ω) ∧
      E.pos x₀ ∈ insideOf (E.walkTrace γ) ∧ E.walkTrace γ ⊆ frontier Ω := by
  have hdisj : Ω ∩ frontier Ω = ∅ := hop.inter_frontier_eq
  have hnot : E.pos x₀ ∉ E.edgesTrace (↑T : Set (Sym2 V)) := by
    intro hmem
    obtain ⟨e, he, hp⟩ := exists_arcOf_of_mem_edgesTrace E hmem
    have : E.pos x₀ ∈ Ω ∩ frontier Ω := ⟨hx, harc e (by simpa using he) hp⟩
    rw [hdisj] at this
    exact this
  have hin : E.pos x₀ ∈ insideOf (E.edgesTrace (↑T : Set (Sym2 V))) :=
    insideOf_of_frontier_subset hop hb hx hcover hnot
  obtain ⟨b, γ, hcyc, hedges, hreg⟩ := hbc T hT (E.pos x₀) hin
  have hlen : γ.length ≠ 0 := by have := hcyc.three_le_length; omega
  have hwt : E.walkTrace γ ⊆ frontier Ω := by
    have hsub : E.walkTrace γ ⊆ E.edgesTrace (↑T : Set (Sym2 V)) :=
      walkTrace_subset_edgesTrace_of_edges E γ (fun g hg => by simpa using hedges g hg) hlen
    intro q hq
    obtain ⟨e, he, hqe⟩ := exists_arcOf_of_mem_edgesTrace E (hsub hq)
    exact harc e (by simpa using he) hqe
  refine ⟨b, γ, hcyc, hedges, mem_cycleRegion_of_insideOf E γ hreg, ?_, hreg, hwt⟩
  intro z hz
  obtain ⟨e, he, hze⟩ := exists_mem_edges_of_mem_support γ hlen hz
  have heT : e ∈ T := hedges e he
  exact harc e heT (pos_mem_arcOf E (hT (by simpa using heT)) hze)

end UCPlanar.Support
