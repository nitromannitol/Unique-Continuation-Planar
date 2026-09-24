/- The face walks of Step 3, reduced to two properties of the plane: the frontier of a face is
covered by whole edge arcs, and it is connected.  Everything combinatorial is proved here: the
edges drawn on the frontier and reachable from one vertex carry a relatively clopen part of the
frontier, so connectedness makes every vertex incident to the face reachable along it. -/
import UCPlanar.Support.TopoClusterEdges
import UCPlanar.Support.TopoLines
import UCPlanar.Support.TopoFacePath
import Mathlib

open Set
open scoped Classical

/-- **The frontier of a face is drawn by a finite set of whole arcs.**  Some finite set of edges
has all its arcs on the frontier of the face and its drawing covers that frontier. -/
def UCPlanar.PlaneEmbedding.FaceFrontierArcs {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) (F : Set UCPlanar.Plane) : Prop :=
  ∃ H : Finset (Sym2 V), ↑H ⊆ G.edgeSet ∧ (∀ e ∈ H, E.arcOf e ⊆ frontier F) ∧
    frontier F ⊆ E.edgesTrace ↑H

namespace UCPlanar.Support

variable {V : Type*} {G : SimpleGraph V}

/-- A drawn vertex on the arc of an edge is one of its two ends. -/
theorem mem_of_pos_mem_arcOf (E : UCPlanar.PlaneEmbedding G) {e : Sym2 V} (he : e ∈ G.edgeSet)
    {z : V} (hz : E.pos z ∈ E.arcOf e) : z ∈ e := by
  induction e with
  | _ x y =>
    have hxy : G.Adj x y := by simpa using he
    rw [arcOf_eq E hxy] at hz
    rcases E.vertex_on_edge hxy z hz with rfl | rfl <;> simp

/-- **A face whose frontier a closed part of the drawing covers is a face of that part.**  The
face is open, misses the part, and is relatively closed in its complement, so it is one of the
connected components there.  With a finite edge set for the part this transports a face of the
whole drawing to a face of a finite plane graph. -/
theorem isFace_eq_connectedComponentIn (Q : UCPlanar.PeriodicPlaneGraph V)
    {F : Set UCPlanar.Plane} (hF : Q.embedding.IsFace F) {X : Set UCPlanar.Plane}
    (hXt : X ⊆ Q.embedding.trace) (hfr : frontier F ⊆ X) {p : UCPlanar.Plane} (hp : p ∈ F) :
    F = connectedComponentIn Xᶜ p := by
  have hop : IsOpen F := isOpen_isFace Q hF
  have hFX : F ⊆ Xᶜ := fun q hq hqX =>
    isFace_subset_compl_trace Q.embedding hF hq (hXt hqX)
  have hsub : F ⊆ connectedComponentIn Xᶜ p :=
    (isFace_isPreconnected Q.embedding hF).subset_connectedComponentIn hp hFX
  refine Set.Subset.antisymm hsub ?_
  have hcov : connectedComponentIn Xᶜ p ⊆ F ∪ (closure F)ᶜ := by
    intro q hq
    by_cases hqF : q ∈ F
    · exact Or.inl hqF
    · refine Or.inr ?_
      intro hcl
      have : q ∈ frontier F := by rw [hop.frontier_eq]; exact ⟨hcl, hqF⟩
      exact (connectedComponentIn_subset _ _ hq) (hfr this)
  have hne : (connectedComponentIn Xᶜ p ∩ F).Nonempty :=
    ⟨p, mem_connectedComponentIn (hFX hp), hp⟩
  have hout : ¬ (connectedComponentIn Xᶜ p ∩ (closure F)ᶜ).Nonempty := by
    intro hne2
    obtain ⟨q, hq1, hq2, hq3⟩ :=
      isPreconnected_connectedComponentIn F (closure F)ᶜ hop isClosed_closure.isOpen_compl
        hcov hne hne2
    exact hq3 (subset_closure hq2)
  intro q hq
  rcases hcov hq with h | h
  · exact h
  · exact absurd ⟨q, hq, h⟩ hout

/-- **The frontier of a face with bounded frontier is drawn by a finite edge set of whole
arcs.**  Only finitely many edges reach a bounded set, so two-sidedness alone gives the finite
boundary edge set. -/
theorem faceFrontierArcs_of_twoSided (Q : UCPlanar.PeriodicPlaneGraph V)
    {F : Set UCPlanar.Plane} (hbdd : Bornology.IsBounded (frontier F))
    (h2 : ∀ p ∈ frontier F, ∃ e ∈ Q.graph.edgeSet,
      p ∈ Q.embedding.arcOf e ∧ Q.embedding.arcOf e ⊆ frontier F) :
    Q.embedding.FaceFrontierArcs F := by
  classical
  set S : Set (Sym2 V) := {e : Sym2 V | e ∈ Q.graph.edgeSet ∧
    (Q.embedding.arcOf e ∩ frontier F).Nonempty ∧ Q.embedding.arcOf e ⊆ frontier F} with hS
  have hfin : S.Finite := by
    refine Set.Finite.subset (finite_edges_meeting_bounded Q hbdd) ?_
    rintro e ⟨he, hne, -⟩
    exact ⟨he, hne⟩
  refine ⟨hfin.toFinset, ?_, ?_, ?_⟩
  · intro e he
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at he
    exact he.1
  · intro e he
    rw [Set.Finite.mem_toFinset] at he
    exact he.2.2
  · intro p hp
    obtain ⟨e, he, hpe, hsub⟩ := h2 p hp
    refine Set.mem_biUnion (?_ : e ∈ (hfin.toFinset : Set (Sym2 V))) hpe
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact ⟨he, ⟨p, hpe, hp⟩, hsub⟩

/-- **Two vertices incident to a face are joined along its frontier.**  The edges of the
boundary set reachable from the first vertex draw a relatively clopen part of the frontier: it is
a finite union of arcs, and the remaining arcs meet it only at vertices, which reachability would
already have swallowed.  Connectedness of the frontier therefore makes it the whole frontier. -/
theorem exists_frontier_walk (E : UCPlanar.PlaneEmbedding G) {F : Set UCPlanar.Plane}
    (hfa : E.FaceFrontierArcs F) (hconn : IsPreconnected (frontier F))
    {u v : V} (hu : E.Incident F u) (hv : E.Incident F v) :
    ∃ β : G.Walk u v, E.walkTrace β ⊆ frontier F := by
  classical
  obtain ⟨H, hHsub, hHarc, hHcov⟩ := hfa
  set R : Set V := {x | ∃ p : G.Walk u x, E.walkTrace p ⊆ frontier F} with hR
  have huR : u ∈ R := by
    refine ⟨SimpleGraph.Walk.nil, ?_⟩
    intro t ht
    have : t = E.pos u := ht
    rw [this]; exact hu
  have hext : ∀ e ∈ H, ∀ a ∈ e, a ∈ R → ∀ z ∈ e, z ∈ R := by
    intro e he a hae haR z hze
    have hearc : E.arcOf e ⊆ frontier F := hHarc e he
    have heset : e ∈ G.edgeSet := hHsub (by simpa using he)
    induction e with
    | _ x y =>
      have hxy : G.Adj x y := by simpa using heset
      have hstep : ∀ s t : V, G.Adj s t → E.arcOf s(s, t) ⊆ frontier F → s ∈ R → t ∈ R := by
        intro s t hst harc hsR
        obtain ⟨p, hp⟩ := hsR
        refine ⟨p.append (SimpleGraph.Walk.cons hst SimpleGraph.Walk.nil), ?_⟩
        rw [E.walkTrace_append]
        refine Set.union_subset hp ?_
        intro q hq
        rcases hq with hq | hq
        · exact harc ((arcOf_eq E hst) ▸ hq)
        · have : q = E.pos t := hq
          rw [this]
          exact harc ((arcOf_eq E hst) ▸ ⟨1, (E.edge hst).target⟩)
      rw [Sym2.mem_iff] at hae hze
      have harcxy : E.arcOf s(x, y) ⊆ frontier F := hearc
      have harcyx : E.arcOf s(y, x) ⊆ frontier F := by
        rw [Sym2.eq_swap]; exact harcxy
      rcases hae with rfl | rfl <;> rcases hze with rfl | rfl
      · exact haR
      · exact hstep _ _ hxy harcxy haR
      · exact hstep _ _ hxy.symm harcyx haR
      · exact haR
  set H₀ : Finset (Sym2 V) := H.filter (fun e => ∃ a, a ∈ e ∧ a ∈ R) with hH₀
  have hH₀sub : H₀ ⊆ H := Finset.filter_subset _ _
  set S : Set UCPlanar.Plane := E.edgesTrace ↑H₀ ∪ {E.pos u} with hSdef
  set S' : Set UCPlanar.Plane := E.edgesTrace ↑(H \ H₀) with hS'def
  have hSclosed : IsClosed S :=
    ((isCompact_edgesTrace E (H₀ : Finset (Sym2 V)).finite_toSet
      (fun e he => hHsub (hH₀sub (by simpa using he)))).isClosed).union isClosed_singleton
  have hS'closed : IsClosed S' :=
    (isCompact_edgesTrace E ((H \ H₀ : Finset (Sym2 V))).finite_toSet
      (fun e he => hHsub (by
        have := Finset.mem_sdiff.mp (by simpa using he)
        simpa using this.1))).isClosed
  have hdisj : S ∩ S' = ∅ := by
    ext q
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hqS hqS'
    obtain ⟨f, hf, hqf⟩ := Set.mem_iUnion₂.mp hqS'
    have hfH : f ∈ H := (Finset.mem_sdiff.mp (by simpa using hf)).1
    have hfnot : f ∉ H₀ := (Finset.mem_sdiff.mp (by simpa using hf)).2
    have hfset : f ∈ G.edgeSet := hHsub (by simpa using hfH)
    rcases hqS with hqS | hqS
    · obtain ⟨e, he, hqe⟩ := Set.mem_iUnion₂.mp hqS
      have heH₀ : e ∈ H₀ := by simpa using he
      have heH : e ∈ H := hH₀sub heH₀
      have heset : e ∈ G.edgeSet := hHsub (by simpa using heH)
      have hne : e ≠ f := fun h => hfnot (h ▸ heH₀)
      obtain ⟨z, hze, hzf, -⟩ := arcOf_inter_arcOf E heset hfset hne hqe hqf
      obtain ⟨a, hae, haR⟩ := (Finset.mem_filter.mp heH₀).2
      exact hfnot (Finset.mem_filter.mpr ⟨hfH, ⟨z, hzf, hext e heH a hae haR z hze⟩⟩)
    · have hqu : q = E.pos u := hqS
      rw [hqu] at hqf
      exact hfnot (Finset.mem_filter.mpr
        ⟨hfH, ⟨u, mem_of_pos_mem_arcOf E hfset hqf, huR⟩⟩)
  have hcover : frontier F ⊆ S ∪ S' := by
    intro q hq
    obtain ⟨e, he, hqe⟩ := Set.mem_iUnion₂.mp (hHcov hq)
    by_cases h : e ∈ H₀
    · exact Or.inl (Or.inl (Set.mem_biUnion (by simpa using h) hqe))
    · exact Or.inr (Set.mem_biUnion
        (by simpa using Finset.mem_sdiff.mpr ⟨by simpa using he, h⟩) hqe)
  have hcov2 : frontier F ⊆ S'ᶜ ∪ Sᶜ := by
    intro t htF
    rcases hcover htF with h | h
    · refine Or.inl (fun hmem => ?_)
      have hc : t ∈ S ∩ S' := ⟨h, hmem⟩
      rw [hdisj] at hc; exact hc
    · refine Or.inr (fun hmem => ?_)
      have hc : t ∈ S ∩ S' := ⟨hmem, h⟩
      rw [hdisj] at hc; exact hc
  have hsubS : frontier F ⊆ S := by
    by_contra hcon
    obtain ⟨q, hqF, hqS⟩ := Set.not_subset.mp hcon
    have hne1 : (frontier F ∩ S'ᶜ).Nonempty := by
      refine ⟨E.pos u, hu, fun hmem => ?_⟩
      have hc : E.pos u ∈ S ∩ S' := ⟨Or.inr rfl, hmem⟩
      rw [hdisj] at hc; exact hc
    have hne2 : (frontier F ∩ Sᶜ).Nonempty := ⟨q, hqF, hqS⟩
    obtain ⟨t, htF, ht1, ht2⟩ :=
      hconn S'ᶜ Sᶜ hS'closed.isOpen_compl hSclosed.isOpen_compl hcov2 hne1 hne2
    rcases hcover htF with h | h
    · exact ht2 h
    · exact ht1 h
  have hvR : v ∈ R := by
    rcases hsubS hv with h | h
    · obtain ⟨e, he, hve⟩ := Set.mem_iUnion₂.mp h
      have heH₀ : e ∈ H₀ := by simpa using he
      have heH : e ∈ H := hH₀sub heH₀
      have heset : e ∈ G.edgeSet := hHsub (by simpa using heH)
      obtain ⟨a, hae, haR⟩ := (Finset.mem_filter.mp heH₀).2
      exact hext e heH a hae haR v (mem_of_pos_mem_arcOf E heset hve)
    · have : E.pos v = E.pos u := h
      rw [E.pos_injective this]; exact huR
  exact hvR

/-- **The face walks, from the two plane properties.**  If the frontier of every face is drawn by
finitely many whole arcs and is connected, the vertices incident to a face are joined along
it. -/
theorem faceWalks_of_frontierArcs (E : UCPlanar.PlaneEmbedding G)
    (hfa : ∀ F, E.IsFace F → E.FaceFrontierArcs F)
    (hconn : ∀ F, E.IsFace F → IsPreconnected (frontier F)) : E.FaceWalks :=
  fun F hF _ _ hu hv => exists_frontier_walk E (hfa F hF) (hconn F hF) hu hv


/-- **A point of the plane inside an open ball keeps the ball when passing to the closure.** -/
theorem mem_closure_inter_ball {p r : UCPlanar.Plane} {ε : ℝ} (hr : r ∈ Metric.ball p ε)
    {A : Set UCPlanar.Plane} (hcl : r ∈ closure A) :
    r ∈ closure (Metric.ball p ε ∩ A) := by
  rw [mem_closure_iff]
  intro W hW hrW
  obtain ⟨t, htW, htA⟩ :=
    (mem_closure_iff.mp hcl) (W ∩ Metric.ball p ε) (hW.inter Metric.isOpen_ball) ⟨hrW, hr⟩
  exact ⟨t, htW.1, htW.2, htA⟩

/-- **Two-sidedness at a point of a straight piece of the drawing.**  If near a point of the
frontier of a face the drawing lies on one line and that line lies on the drawing, then the whole
piece of the line near the point is on the frontier of the face: a side of the line near the
point is a convex set missing the drawing, so it lies in the face, and the line lies in the
closure of each of its sides. -/
theorem ball_inter_lineSet_subset_frontier (Q : UCPlanar.PeriodicPlaneGraph V)
    {F : Set UCPlanar.Plane} (hF : Q.embedding.IsFace F)
    {p : UCPlanar.Plane} {ε : ℝ} (hε : 0 < ε) {l : ℝ × ℝ × ℝ} (hl : l.1 ≠ 0 ∨ l.2.1 ≠ 0)
    (hline : Metric.ball p ε ∩ Q.embedding.trace ⊆ lineSet l)
    (harc : Metric.ball p ε ∩ lineSet l ⊆ Q.embedding.trace)
    (hp : p ∈ frontier F) :
    Metric.ball p ε ∩ lineSet l ⊆ frontier F := by
  classical
  obtain ⟨p₀, hp₀, rfl⟩ := hF
  have hcl : p ∈ closure (connectedComponentIn Q.embedding.traceᶜ p₀) := hp.1
  obtain ⟨q, hqb, hqF⟩ :=
    (mem_closure_iff.mp hcl) (Metric.ball p ε) Metric.isOpen_ball (Metric.mem_ball_self hε)
  have hqt : q ∉ Q.embedding.trace := connectedComponentIn_subset _ _ hqF
  have hql : q ∉ lineSet l := fun hc => hqt (harc ⟨hqb, hc⟩)
  obtain ⟨s, hs⟩ := exists_mem_halfPlane hql
  set K : Set UCPlanar.Plane := Metric.ball p ε ∩ halfPlane s l with hK
  have hKconv : Convex ℝ K := (convex_ball p ε).inter (convex_halfPlane s l)
  have hKt : K ⊆ Q.embedding.traceᶜ := by
    rintro x ⟨hx1, hx2⟩ hx3
    exact halfPlane_subset_compl_lineSet s l hx2 (hline ⟨hx1, hx3⟩)
  have hKF : K ⊆ connectedComponentIn Q.embedding.traceᶜ p₀ := by
    have h1 : K ⊆ connectedComponentIn Q.embedding.traceᶜ q :=
      hKconv.isPreconnected.subset_connectedComponentIn ⟨hqb, hs⟩ hKt
    rw [connectedComponentIn_eq hqF]
    exact h1
  rintro r ⟨hr1, hr2⟩
  have hrcl : r ∈ closure K :=
    mem_closure_inter_ball hr1 (lineSet_subset_closure_halfPlane l hl s hr2)
  have hrF : r ∈ closure (connectedComponentIn Q.embedding.traceᶜ p₀) :=
    closure_mono hKF hrcl
  have hrnot : r ∉ connectedComponentIn Q.embedding.traceᶜ p₀ := fun hc =>
    (connectedComponentIn_subset _ _ hc) (harc ⟨hr1, hr2⟩)
  rw [(isOpen_isFace Q ⟨p₀, hp₀, rfl⟩).frontier_eq]
  exact ⟨hrF, hrnot⟩


/-- **A connected set has no isolated point unless it is a single point.**  If a neighbourhood of
a point of the set meets it only in that point, the set is that point alone.  This is what
removes the corners of a polygonal arc from the frontier of a face: a corner on the frontier
whose two segments miss the frontier would be isolated in it. -/
theorem eq_singleton_of_isolated {X : Type*} [TopologicalSpace X] [T1Space X] {S : Set X}
    (hS : IsPreconnected S) {c : X} (hc : c ∈ S) {U : Set X} (hU : IsOpen U) (hcU : c ∈ U)
    (hiso : S ∩ U ⊆ {c}) : S ⊆ {c} := by
  intro x hx
  by_contra hxc
  have hcov : S ⊆ U ∪ ({c} : Set X)ᶜ := by
    intro y hy
    by_cases hyc : y = c
    · exact Or.inl (hyc ▸ hcU)
    · exact Or.inr hyc
  obtain ⟨t, htS, htU, htc⟩ :=
    hS U ({c} : Set X)ᶜ hU isClosed_singleton.isOpen_compl hcov ⟨c, hc, hcU⟩ ⟨x, hx, hxc⟩
  exact htc (hiso ⟨htS, htU⟩)

end UCPlanar.Support
